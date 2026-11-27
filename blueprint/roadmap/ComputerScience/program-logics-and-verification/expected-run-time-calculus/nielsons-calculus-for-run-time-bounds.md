# Nielson's calculus for run-time bounds

The *deterministic programs* $\mathrm{dProgs}$ are $C ::= \mathtt{skip} \mid x := E \mid C; C \mid \mathbf{if}\ (\xi)\ \{C\}\ \mathbf{else}\ \{C\} \mid \mathbf{while}\ (\xi)\ \{C\}$ with deterministic expressions $E$ and guards $\xi$. A correctness property $\{P\}\, C\, \{E \Downarrow Q\}$, with first-order assertions $P$, $Q$ and a deterministic expression $E$, is *valid* if there is $k \in \mathbb{N}$ such that from every state $\sigma$ satisfying $P$ the program $C$ terminates after at most $k \cdot [\![E]\!](\sigma)$ steps in a state satisfying $Q$, where a step is an execution of $\mathtt{skip}$ or of an assignment. Guard evaluations take no time in this calculus, unlike the [run-time model](probabilistic-programs-with-a-run-time-model.md) of the expected run-time transformer, which charges one unit for each; for example $\mathbf{if}\ (\mathrm{true})\ \{\mathtt{skip}\}\ \mathbf{else}\ \{\mathtt{skip}\}$ takes one step here and two units there. Since validity allows a constant factor $k$, the two models are compared only up to a multiplicative constant. Nielson's inference system derives such properties, written $\vdash_E \{P\}\, C\, \{E \Downarrow Q\}$, by the rules

- $\{P\}\ \mathtt{skip}\ \{1 \Downarrow P\}$ and $\{Q[x/[\![E]\!]]\}\ x := E\ \{1 \Downarrow Q\}$;
- from $\{P \wedge E_2' = u\}\, C_1\, \{E_1 \Downarrow Q \wedge E_2 \le u\}$ and $\{Q\}\, C_2\, \{E_2 \Downarrow R\}$ infer $\{P\}\, C_1; C_2\, \{E_1 + E_2' \Downarrow R\}$, for a fresh logical variable $u$;
- from $\{P \wedge \xi\}\, C_1\, \{E \Downarrow Q\}$ and $\{P \wedge \neg\xi\}\, C_2\, \{E \Downarrow Q\}$ infer $\{P\}\ \mathbf{if}\ (\xi)\ \{C_1\}\ \mathbf{else}\ \{C_2\}\ \{E \Downarrow Q\}$;
- from $\{P(z + 1) \wedge E' = u\}\, C\, \{E_1 \Downarrow P(z) \wedge E \le u\}$ infer $\{\exists z.\, P(z)\}\ \mathbf{while}\ (\xi)\ \{C\}\ \{E \Downarrow P(0)\}$, where $z$ ranges over $\mathbb{N}$, $P(z + 1) \Rightarrow \xi \wedge E \ge E_1 + E'$, $P(0) \Rightarrow \neg\xi \wedge E \ge 1$ and $u$ is fresh;
- from $\{P'\}\, C\, \{E' \Downarrow Q'\}$ infer $\{P\}\, C\, \{E \Downarrow Q\}$ when $P \Rightarrow P' \wedge E' \le k \cdot E$ for some $k \in \mathbb{N}$ and $Q' \Rightarrow Q$.

Omitting the run-time expressions gives the standard Hoare calculus for total correctness, whose derivability is written $\vdash \{P\}\, C\, \{\Downarrow Q\}$.

## Depends on

- [Probabilistic programs with a run-time model](probabilistic-programs-with-a-run-time-model.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 6 and Figure 4 (taken from H. R. Nielson and F. Nielson, *Semantics with Applications: An Appetizer*, Springer, 2007, after H. R. Nielson, "A Hoare-like proof system for analysing the computation time of programs", *Science of Computer Programming* 9(2):107–136, 1987).
