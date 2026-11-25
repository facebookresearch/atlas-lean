# SLD resolution

Let $P$ be a definite logic program and $\vec A, B, \vec C$ a query, a finite sequence of atoms with a selected atom $B$.

- **SLD step.** Let $c \in P$ be a clause and $H \leftarrow \vec B$ a variant of $c$ that is variable disjoint from the query. If $\theta$ is a most general unifier of $B$ and $H$, the *SLD resolvent* is $(\vec A, \vec B, \vec C)\theta$, and $\vec A, B, \vec C \overset{\theta}{\Longrightarrow} (\vec A, \vec B, \vec C)\theta$ is an SLD derivation step with input clause $H \leftarrow \vec B$.
- **SLD derivation.** An SLD derivation is a finite or infinite sequence of steps $Q_0 \overset{\theta_1}{\Longrightarrow} Q_1 \overset{\theta_2}{\Longrightarrow} \cdots$. Its input clauses must be *standardized apart*: each one is variable disjoint from the initial query and from the substitutions and input clauses of all earlier steps.
- **Success and failure.** A finite derivation is *successful* if it ends in the empty query $\square$. It is *failed* if it ends in a nonempty query to whose selected atom no clause is applicable.
- **Computed answers.** For a successful derivation the *computed answer substitution* of $Q_0$ is $(\theta_1 \cdots \theta_n)|_{\mathrm{Var}(Q_0)}$, and $Q_0\theta_1 \cdots \theta_n$ is the computed instance.
- **Selection rules.** A *selection rule* is a function giving, for every initial fragment of a derivation that ends in a nonempty query, an occurrence of an atom in that query. A derivation is *via* a selection rule $R$ if each selected atom is the one chosen by $R$. Prolog selects the leftmost atom.

**Independence of the selection rule.** If $P \cup \{Q_0\}$ has a successful SLD derivation, then for every selection rule $R$ it has a successful SLD derivation via $R$ of the same length and with the same computed answer substitution.

## Sources

- H. Strass (based on slides by M. Thielscher), *SLD Resolution*, Lecture 3 of Foundations of Logic Programming, TU Dresden, 2026, <https://iccl.inf.tu-dresden.de/w/images/b/b2/FLP2026-03.pdf>: the definitions of SLD resolvent, derivation step and input clause, standardization apart, successful and failed derivations, computed answer substitutions, selection rules, and Theorem 3.33 (independence of the selection rule).
- J. W. Lloyd, *Foundations of Logic Programming*, 2nd ed., Springer, 1987.
