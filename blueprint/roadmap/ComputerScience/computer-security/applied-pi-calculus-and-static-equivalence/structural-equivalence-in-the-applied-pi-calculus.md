# Structural equivalence in the applied pi calculus

Fix a signature with an equational theory, a congruence on terms closed under substitution of terms for variables and names that respects sorts and is
nontrivial in each sort (some two terms of the sort are not equated), written $\Sigma \vdash M = N$ (see [equational theories](equational-theories-and-convergent-subterm-theories.md)). *Structural equivalence* $\equiv$ is the smallest
equivalence relation on the [extended processes](terms-and-processes-of-the-applied-pi-calculus.md) that is closed under application of evaluation contexts and satisfies

$$\begin{aligned}
&A \mid 0 \equiv A, \quad (A \mid B) \mid C \equiv A \mid (B \mid C), \quad A \mid B \equiv B \mid A, \quad !P \equiv P \mid\ !P, \quad \nu n.0 \equiv 0, \quad \nu u.\nu v.A \equiv \nu v.\nu u.A,\\
&A \mid \nu u.B \equiv \nu u.(A \mid B) \text{ when } u \notin \mathrm{fv}(A) \cup \mathrm{fn}(A), \quad \nu x.\{M/x\} \equiv 0, \quad \{M/x\} \mid A \equiv \{M/x\} \mid A\{M/x\},\\
&\{M/x\} \equiv \{N/x\} \text{ when } \Sigma \vdash M = N
\end{aligned}$$

(the rules Par-0, Par-A, Par-C, Repl, New-0, New-C, New-Par, Alias, Subst and Rewrite). Every closed extended process $A$ is structurally equivalent to
$\nu\tilde n.(\{\tilde M/\tilde x\} \mid P)$ with $P$ a closed plain process ($\mathrm{fv}(P) = \emptyset$), ground images ($\mathrm{fv}(\tilde M) = \emptyset$) and $\tilde n \subseteq \mathrm{fn}(\tilde M)$, and every closed
frame $\varphi$ to $\nu\tilde n.\{\tilde M/\tilde x\}$ with $\mathrm{fv}(\tilde M) = \emptyset$ and $\tilde n \subseteq \mathrm{fn}(\tilde M)$; the variables $\tilde x$ are exactly the domain. For example, the closed frame
$\{a/x\} \mid \{x/y\}$ is equivalent to $\{a/x\} \mid \{a/y\}$.

## Depends on

- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)
- [Equational theories and convergent subterm theories](equational-theories-and-convergent-subterm-theories.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 2.2, the definition of equational theories (respecting sorts and non-trivial, with two different terms in each sort) and of structural equivalence, and the normal form of closed extended processes and closed frames that follows it ($\mathrm{fv}(P) = \mathrm{fv}(\tilde M) = \emptyset$ and $\tilde n \subseteq \mathrm{fn}(\tilde M)$).
