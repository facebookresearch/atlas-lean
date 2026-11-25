# Pure type systems and the calculus of constructions

Pure type systems, also called generalized type systems, share one set of pseudoterms

$$T ::= x \mid c \mid T\,T \mid \lambda x{:}T.\, T \mid \Pi x{:}T.\, T,$$

where $x$ ranges over variables and $c$ over a set $C$ of constants.

- **Specifications.** A specification is a triple $(\mathcal{S}, \mathcal{A}, \mathcal{R})$. The sorts are a subset $\mathcal{S} \subseteq C$, the axioms $\mathcal{A}$ are statements $c : s$ with $c \in C$ and $s \in \mathcal{S}$, and the rules $\mathcal{R}$ are triples $(s_1, s_2, s_3)$ of sorts. A rule $(s_1, s_2)$ abbreviates $(s_1, s_2, s_2)$.
- **Typing rules.** The system $\lambda(\mathcal{S}, \mathcal{A}, \mathcal{R})$ derives judgments $\Gamma \vdash A : B$ by the following rules, where $x$ is fresh in the start and weakening rules:
    - **axiom:** $\vdash c : s$ for $(c : s) \in \mathcal{A}$;
    - **start:** from $\Gamma \vdash A : s$ infer $\Gamma, x{:}A \vdash x : A$;
    - **weakening:** from $\Gamma \vdash B : C$ and $\Gamma \vdash A : s$ infer $\Gamma, x{:}A \vdash B : C$;
    - **product:** from $\Gamma \vdash A : s_1$ and $\Gamma, x{:}A \vdash B : s_2$ infer $\Gamma \vdash (\Pi x{:}A.\, B) : s_3$, for $(s_1, s_2, s_3) \in \mathcal{R}$;
    - **abstraction:** from $\Gamma \vdash A : s_1$, $\Gamma, x{:}A \vdash B : s_2$ and $\Gamma, x{:}A \vdash b : B$ infer $\Gamma \vdash (\lambda x{:}A.\, b) : (\Pi x{:}A.\, B)$, for some $(s_1, s_2, s_3) \in \mathcal{R}$;
    - **application:** from $\Gamma \vdash F : (\Pi x{:}A.\, B)$ and $\Gamma \vdash a : A$ infer $\Gamma \vdash F\,a : B[x := a]$;
    - **conversion:** from $\Gamma \vdash A : B$, $\Gamma \vdash B' : s$ and $B =_\beta B'$ infer $\Gamma \vdash A : B'$.
- **The calculus of constructions.** The calculus of constructions $\lambda C$ is the system with sorts $\{*, \square\}$, the axiom $* : \square$ and the rules $(*, *)$, $(\square, *)$, $(*, \square)$, $(\square, \square)$. Since it contains all four pairs of sorts, it is the full system on $\{*, \square\}$. The systems of the $\lambda$-cube are those with the same sorts and axiom, the rule $(*, *)$, and any subset of the other three rules.
- **Metatheory.** For every system of the $\lambda$-cube, typing is closed under $\beta$-reduction of the subject (subject reduction), every typable term is strongly normalizing, and types are unique up to $\beta$-conversion. Subject reduction holds for every pure type system, but uniqueness of types can fail.
- **An inconsistent system.** The system $\lambda{*}$, with the single sort $*$, the axiom $* : *$ and the rule $(*, *)$, is inconsistent: every type is inhabited (Girard's paradox).

## Sources

- H. Barendregt, "Introduction to generalized type systems", *Journal of Functional Programming* 1(2):125–154, 1991, <https://homepages.inf.ed.ac.uk/wadler/papers/barendregt/pure-type-systems.pdf>: Definitions 3.1–3.3 (specifications, typing rules and full systems), Examples 3.4 ($\lambda C$ and $\lambda{*}$, with Girard's paradox), the remark on subject reduction for all systems, and Theorems 2.4–2.6 (subject reduction, strong normalization and uniqueness of types for the $\lambda$-cube).
- H. P. Barendregt, "Lambda calculi with types", in *Handbook of Logic in Computer Science*, vol. 2, Oxford University Press, 1992.
