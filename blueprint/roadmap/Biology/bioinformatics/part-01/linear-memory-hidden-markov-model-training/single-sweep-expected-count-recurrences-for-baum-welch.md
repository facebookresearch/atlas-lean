# Single-sweep expected-count recurrences for Baum–Welch

**Setting.** An HMM with states $1,\dots,N$, transition probabilities $a_{i,j}$, emission probabilities $b_m(o)$ over symbols $\gamma \in \{1,\dots,D\}$, observations $o_1,\dots,o_T$, and forward variables $\alpha_t(m) = \Pr(o_1,\dots,o_t, q_t = m)$; $Q_{\max}$ is the maximum in-degree of a state.

**Transition counts.** Let $t_{i,j}(t,m)$ be the sum, over state paths emitting $o_1,\dots,o_t$ and ending in $m$, of the path probability weighted by the number of $i\to j$ transitions it uses. Then $t_{i,j}(1,m) = 0$ and

$$t_{i,j}(t,m) = \alpha_{t-1}(i)\,a_{i,m}\,b_m(o_t)\,\mathbf 1[m = j] + \sum_{n=1}^N t_{i,j}(t-1,n)\,a_{n,m}\,b_m(o_t).$$

**Emission counts.** Let $e_i(\gamma,t,m)$ be the analogous weighted sum with weight the number of emissions of $\gamma$ from state $i$. Then $e_i(\gamma,1,m) = \alpha_1(m)\mathbf 1[i = m]\mathbf 1[\gamma = o_1]$ and

$$e_i(\gamma,t,m) = \alpha_t(m)\,\mathbf 1[i = m]\,\mathbf 1[\gamma = o_t] + \sum_{n=1}^N e_i(\gamma,t-1,n)\,a_{n,m}\,b_m(o_t).$$

**Theorem.** The recurrences compute these weighted path sums, so with $t^{\mathrm{END}}_{i,j} = \sum_m t_{i,j}(T,m)$ and $e^{\mathrm{END}}_i(\gamma) = \sum_m e_i(\gamma,T,m)$ the Baum–Welch updates are

$$\hat a_{i,j} = \frac{t^{\mathrm{END}}_{i,j}}{\sum_{j'\in\mathrm{out}(i)} t^{\mathrm{END}}_{i,j'}}, \qquad \hat b_i(\gamma) = \frac{e^{\mathrm{END}}_i(\gamma)}{\sum_{\gamma'} e^{\mathrm{END}}_i(\gamma')}.$$

Only the previous time slice is needed, so memory is $O(NQ)$ for transitions and $O(NED)$ for emissions ($E$ states with free emissions), independent of $T$, at time cost $O(TNQQ_{\max})$ and $O(TNEDQ_{\max})$. The mirror-image backward sweep with scaled backward probabilities $\tilde\beta_t = d_t\beta_t$ yields the same estimates, since every scaled count is the true count times the same factor $D_1$, which cancels in each ratio, and it also gives the initial-state estimate $\hat\pi_i \propto \alpha_1(i)\beta_1(i)$.

## Depends on

- [Forward variables of a hidden Markov model](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/forward.md)
- [Backward variables of a hidden Markov model](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/backward.md)

## Expansion

A path that uses $i \to j$ at step $t$ contributes $\alpha_{t-1}(i)a_{i,j}b_j(o_t)$ times its future, so the first term injects new evidence at time $t$ and the second propagates earlier evidence forward along all transitions; induction on $t$ proves the path-sum interpretation, and summing over the final state gives the numerator $\sum_t\Pr(q_{t-1} = i, q_t = j, o_{1:T})$ of the standard update. Viterbi decoding can likewise avoid a full pointer table: keeping two score columns and storing back-pointers as linked nodes lets unreferenced partial paths be freed once all surviving back-traces coalesce, which in practice gives near-linear memory in $T$, compared with $O(N\sqrt T + T)$ for checkpointing.

## Sources

- A. Churbanov, S. Winters-Hilt, "Implementing EM and Viterbi algorithms for Hidden Markov Model in linear memory", BMC Bioinformatics 9 (2008) 224, Methods (forward sweep strategy), Eqs (3)–(10), Theorem 1 and Appendix A (Theorems 2–4), <https://doi.org/10.1186/1471-2105-9-224>, PMCID PMC2430973.
