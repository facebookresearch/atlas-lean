# Operational Markov decision process of a probabilistic program

For a [program](probabilistic-programs-with-a-run-time-model.md) $C$, an initial state $\sigma_0$ and a continuation [run-time](run-times.md) $f$, the *operational MDP* $M^f_{\sigma_0}[\![C]\!] = (S, \mathit{Act}, P, s_0, \mathit{rew})$ is the [Markov decision process with state rewards](expected-reward-of-reaching-a-target-in-a-markov-decision-process.md) with states $S = ((\mathrm{pProgs} \cup \{\downarrow\} \cup \{\downarrow; C' \mid C' \in \mathrm{pProgs}\}) \times \Sigma) \cup \{\langle \mathit{sink} \rangle\}$, actions $\{L, \tau, R\}$, initial state $\langle C, \sigma_0 \rangle$ and the following transitions:

- $\langle \downarrow, \sigma \rangle \to \langle \mathit{sink} \rangle$, $\langle \mathit{sink} \rangle \to \langle \mathit{sink} \rangle$, $\langle \mathtt{empty}, \sigma \rangle \to \langle \downarrow, \sigma \rangle$, $\langle \mathtt{skip}, \sigma \rangle \to \langle \downarrow, \sigma \rangle$ and $\langle \mathtt{halt}, \sigma \rangle \to \langle \mathit{sink} \rangle$, each with probability $1$ under $\tau$;
- $\langle x :\approx \mu, \sigma \rangle \to \langle \downarrow, \sigma[x/v] \rangle$ with probability $[\![\mu : v]\!](\sigma)$, for each $v$ with positive probability;
- if $\langle C_1, \sigma \rangle \xrightarrow{\alpha} \langle C_1', \sigma' \rangle$ with probability $p$ then $\langle C_1; C_2, \sigma \rangle \xrightarrow{\alpha} \langle C_1'; C_2, \sigma' \rangle$ with probability $p$, and $\langle \downarrow; C_2, \sigma \rangle \to \langle C_2, \sigma \rangle$;
- $\langle \{C_1\} \,\square\, \{C_2\}, \sigma \rangle$ moves to $\langle C_1, \sigma \rangle$ under $L$ and to $\langle C_2, \sigma \rangle$ under $R$;
- the conditional moves to $\langle C_1, \sigma \rangle$ with probability $[\![\xi : \mathrm{true}]\!](\sigma)$ and to $\langle C_2, \sigma \rangle$ with probability $[\![\xi : \mathrm{false}]\!](\sigma)$;
- $\langle \mathbf{while}\ (\xi)\ \{C'\}, \sigma \rangle \to \langle \mathbf{if}\ (\xi)\ \{C'; \mathbf{while}\ (\xi)\ \{C'\}\}\ \mathbf{else}\ \{\mathtt{empty}\}, \sigma \rangle$.

The reward is $f(\sigma)$ in $\langle \downarrow, \sigma \rangle$; $1$ in states $\langle \mathtt{skip}, \sigma \rangle$, $\langle x :\approx \mu, \sigma \rangle$ and conditionals; $\mathit{rew}(\langle C_1, \sigma \rangle)$ in $\langle C_1; C_2, \sigma \rangle$; and $0$ in all other states.

## Depends on

- [Probabilistic programs with a run-time model](probabilistic-programs-with-a-run-time-model.md)
- [Expected reward of reaching a target in a Markov decision process](expected-reward-of-reaching-a-target-in-a-markov-decision-process.md)
- [Run-times](run-times.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 4, Definition 2, Figure 2 and Table 2.
