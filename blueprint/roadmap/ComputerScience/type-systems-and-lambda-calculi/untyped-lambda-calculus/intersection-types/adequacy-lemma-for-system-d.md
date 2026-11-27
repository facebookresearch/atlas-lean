# Adequacy lemma for system D

Let $N$ be the set of strongly β-normalizing untyped terms and $N_0$ the set of terms $x\, t_1 \cdots t_n$ with $x$ a variable and $t_1, \dots, t_n \in N$. A set $X$ of terms is
*$N$-saturated* if $(u[t/x])\, t_1 \cdots t_n \in X$ implies $(\lambda x.\, u)\, t\, t_1 \cdots t_n \in X$ for every $t \in N$; an *$N$-interpretation* assigns $N$-saturated sets to
type variables and extends to types of [system D](intersection-type-system-d.md) by $|B \to C| = |B| \to |C|$, where for sets $X, Y$ of terms
$X \to Y = \{u : u\, v \in Y \text{ for every } v \in X\}$ (not a function space), and $|B \wedge C| = |B| \cap |C|$. Then:

1. $N$ is $N$-saturated, $N_0 \subseteq N$, $N_0 \subseteq N \to N_0$ and $N_0 \to N \subseteq N$;
2. if $|X|_I$ is an $N$-saturated set with $N_0 \subseteq |X|_I \subseteq N$ for every type variable, then $N_0 \subseteq |A|_I \subseteq N$ for every type $A$;
3. (adequacy) under that assumption, if $x_1 : A_1, \dots, x_k : A_k \vdash_D u : A$ and $t_i \in |A_i|_I$, then $u[t_1/x_1, \dots, t_k/x_k] \in |A|_I$.

Taking $t_i = x_i \in N_0$ gives that every term typable in D is strongly normalizing. Part 1 uses that the reduction sequences from a strongly normalizing term have bounded length (Kőnig's lemma, since a term
has only finitely many one-step reducts).

## Depends on

- [The intersection type system D](intersection-type-system-d.md)
- [β-reduction](../beta-reduction-and-confluence/beta-reduction.md)

## Proof depends on

- [Kőnig's lemma for inverse systems](../../../process-calculi/csp-semantic-models/konig-s-lemma-for-inverse-systems.md): with the reduction sequences of length $i$ from a term as the $i$-th level, each with finitely many one-step extensions, unbounded lengths would give an infinite reduction sequence

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 3, Section 2: the definitions of $N$-saturated sets and $N$-interpretations, Propositions 3.15, 3.18 and 3.19, Lemmas 3.16 (adequacy) and 3.17, and the verification that $(N_0, N)$ is an adapted pair before Theorem 3.20.
