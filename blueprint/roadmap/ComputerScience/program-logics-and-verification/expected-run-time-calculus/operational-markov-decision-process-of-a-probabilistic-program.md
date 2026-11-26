# Operational Markov decision process of a probabilistic program

For a [program](probabilistic-programs-with-a-run-time-model.md) $C$, an initial state $\sigma_0$ and a continuation [run-time](run-times.md) $f$, the *operational MDP* $M^f_{\sigma_0}[\![C]\!] = (S, \mathit{Act}, P, s_0, \mathit{rew})$ is the [Markov decision process with state rewards](expected-reward-of-reaching-a-target-in-a-markov-decision-process.md) defined as follows. *Residual commands* are given by $R ::= C' \mid {\downarrow} \mid R; C'$ with $C' \in \mathrm{pProgs}$, so that a residual keeps every pending right operand of a sequence; the *head* of a residual is $\mathrm{hd}(R; C') = \mathrm{hd}(R)$ and $\mathrm{hd}(R) = R$ otherwise. The actions are $\{L, \tau, R\}$, the initial state is $s_0 = \langle C, \sigma_0 \rangle$, and $S$ consists of $\langle \mathit{sink} \rangle$ and the pairs $\langle R, \sigma \rangle$ of a residual and a program state reachable from $s_0$ by the following transitions (a countable set, since every transition has countable support):

- $\langle \downarrow, \sigma \rangle \to \langle \mathit{sink} \rangle$, $\langle \mathit{sink} \rangle \to \langle \mathit{sink} \rangle$, $\langle \mathtt{empty}, \sigma \rangle \to \langle \downarrow, \sigma \rangle$, $\langle \mathtt{skip}, \sigma \rangle \to \langle \downarrow, \sigma \rangle$ and $\langle \mathtt{halt}, \sigma \rangle \to \langle \mathit{sink} \rangle$, each with probability $1$ under $\tau$;
- $\langle x :\approx \mu, \sigma \rangle \to \langle \downarrow, \sigma[x/v] \rangle$ with probability $[\![\mu : v]\!](\sigma)$, for each $v$ with positive probability;
- for $R_1 \ne {\downarrow}$: if $\langle R_1, \sigma \rangle \xrightarrow{\alpha} \langle R_1', \sigma' \rangle$ with probability $p$ then $\langle R_1; C_2, \sigma \rangle \xrightarrow{\alpha} \langle R_1'; C_2, \sigma' \rangle$ with probability $p$, and if $\langle R_1, \sigma \rangle \xrightarrow{\alpha} \langle \mathit{sink} \rangle$ with probability $p$ then $\langle R_1; C_2, \sigma \rangle \xrightarrow{\alpha} \langle \mathit{sink} \rangle$ with probability $p$, so that $\mathtt{halt}$ aborts all further execution; and $\langle \downarrow; C_2, \sigma \rangle \to \langle C_2, \sigma \rangle$ with probability $1$ under $\tau$;
- $\langle \{C_1\} \,\square\, \{C_2\}, \sigma \rangle$ moves to $\langle C_1, \sigma \rangle$ under $L$ and to $\langle C_2, \sigma \rangle$ under $R$;
- the conditional moves to $\langle C_1, \sigma \rangle$ with probability $[\![\xi : \mathrm{true}]\!](\sigma)$ and to $\langle C_2, \sigma \rangle$ with probability $[\![\xi : \mathrm{false}]\!](\sigma)$;
- $\langle \mathbf{while}\ (\xi)\ \{C'\}, \sigma \rangle \to \langle \mathbf{if}\ (\xi)\ \{C'; \mathbf{while}\ (\xi)\ \{C'\}\}\ \mathbf{else}\ \{\mathtt{empty}\}, \sigma \rangle$.

The reward, a value in $[0, \infty]$, is $f(\sigma)$ in $\langle \downarrow, \sigma \rangle$; $1$ in $\langle R, \sigma \rangle$ when $\mathrm{hd}(R)$ is $\mathtt{skip}$, an assignment or a conditional; and $0$ in all other states, in particular in $\langle R, \sigma \rangle$ with $\mathrm{hd}(R) = {\downarrow} \ne R$, when execution advances past an intermediate termination. For example, $\langle \mathtt{halt}; \mathtt{skip}, \sigma \rangle$ moves to $\langle \mathit{sink} \rangle$ with total reward $0$, and $(\mathtt{skip}; \mathtt{skip}); \mathtt{skip}$ collects reward $3$ before reaching $\langle \downarrow, \sigma \rangle$.

The source's Figure 2 lifts through a sequence only transitions to configurations and lists only the residuals $\downarrow; C'$; the residual grammar and the lifted transition to $\langle \mathit{sink} \rangle$ implement its statement in Section 2 that $\mathtt{halt}$ aborts all further execution.

## Depends on

- [Probabilistic programs with a run-time model](probabilistic-programs-with-a-run-time-model.md)
- [Expected reward of reaching a target in a Markov decision process](expected-reward-of-reaching-a-target-in-a-markov-decision-process.md)
- [Run-times](run-times.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 4, Definition 2, Figure 2 and Table 2.
