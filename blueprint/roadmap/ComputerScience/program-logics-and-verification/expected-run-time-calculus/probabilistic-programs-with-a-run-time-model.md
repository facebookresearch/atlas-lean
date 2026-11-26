# Probabilistic programs with a run-time model

Let $\mathrm{Var}$ be a set of program variables with values in $\mathrm{Val}$, and $\Sigma = \{\sigma \mid \sigma : \mathrm{Var} \to \mathrm{Val}\}$ the set of program states. A *distribution expression* $\mu$ denotes a function $[\![\mu]\!] : \Sigma \to \mathcal{D}(\mathrm{Val})$ to discrete probability distributions of total mass $1$, and $[\![\mu : v]\!](\sigma)$ is the probability that $[\![\mu]\!](\sigma)$ assigns to $v$; a probabilistic guard $\xi$ is a distribution expression over truth values, and deterministic expressions are the Dirac cases. The probabilistic programs $\mathrm{pProgs}$ are

$$C ::= \mathtt{empty} \mid \mathtt{skip} \mid \mathtt{halt} \mid x :\approx \mu \mid C; C \mid \{C\} \,\square\, \{C\} \mid \mathbf{if}\ (\xi)\ \{C\}\ \mathbf{else}\ \{C\} \mid \mathbf{while}\ (\xi)\ \{C\}.$$

$\mathtt{empty}$ has no effect and takes no time; $\mathtt{skip}$ has no effect and takes one unit of time; $\mathtt{halt}$ aborts the execution and takes no time; $x :\approx \mu$ samples a value from $[\![\mu]\!](\sigma)$, assigns it to $x$ and takes one unit; $\{C_1\} \,\square\, \{C_2\}$ is a demonic nondeterministic choice; the conditional executes $C_1$ with probability $[\![\xi : \mathrm{true}]\!]$ and $C_2$ otherwise; the loop executes its body followed by the loop with probability $[\![\xi : \mathrm{true}]\!]$ and stops otherwise; each guard evaluation takes one unit of time. A program is *fully probabilistic* if it contains no nondeterministic choice.

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 2.
