# Abstract Gödel–Rosser incompleteness theorem

Let $\mathcal{L}$ be a set of formulas with
operations $\neg$ and $\to$, a substitution map sending $A \in \mathcal{L}$ and $n \in \mathbb{N}$
to $A[n] \in \mathcal{L}$, a coding map $\ulcorner \cdot \urcorner : \mathcal{L} \to \mathbb{N}$,
a formula $R \in \mathcal{L}$, predicates "provable" (written $\vdash A$), "Rosser provable" and
"true" on $\mathcal{L}$, and a proof relation $\mathrm{Prf}(A, n)$ between formulas $A$ and
natural numbers $n$. Assume that, for all formulas $A$, $B$ and all $n$:
(i) $\neg A$ is true if and only if $A$ is not true;
(ii) if $\vdash A \to B$ and $\vdash A$, then $\vdash B$;
(iii) $\vdash A$ and $\vdash \neg A$ do not both hold;
(iv) $(\neg A)[n] = \neg (A[n])$;
(v) $\vdash A$ if and only if $\mathrm{Prf}(A, k)$ for some $k$;
(vi) $A$ is Rosser provable if and only if there is $k$ with $\mathrm{Prf}(A, k)$ and there is no
$m < k$ with $\mathrm{Prf}(\neg A, m)$;
(vii) $R[\ulcorner A \urcorner]$ is true if and only if $A$ is Rosser provable;
(viii) if $A$ is Rosser provable, then $\vdash R[\ulcorner A \urcorner]$;
(ix) if $\vdash \neg A$, then $\vdash \neg R[\ulcorner A \urcorner]$;
(x) for every formula $F$ there is a formula $G$ with $G[k] = G$ for all $k$,
$\vdash G \to F[\ulcorner G \urcorner]$ and $\vdash F[\ulcorner G \urcorner] \to G$, such that
$G$ is true if and only if $F[\ulcorner G \urcorner]$ is true.
Then there is a formula $G$ with $G[k] = G$ for all $k$ such that $G$ is true, $\nvdash G$ and
$\nvdash \neg G$.

These hypotheses are assumed as an interface; they are not derived from a concrete effective
arithmetic syntax.

Proof: Apply diagonalization to the negation of the Rosser provability formula, then use
consistency and representability as in Rosser (1936) and Smith, 2nd ed., Chapter 25.

## Sources

- Kurt Gödel, *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*, Monatshefte für Mathematik und Physik 38 (1931), 173–198; J. Barkley Rosser, *Extensions of some theorems of Gödel and Church*, Journal of Symbolic Logic 1 (1936), 87–91.
