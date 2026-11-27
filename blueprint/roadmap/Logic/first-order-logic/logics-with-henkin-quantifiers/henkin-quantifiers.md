# Henkin quantifiers

A Henkin, or branching, quantifier is a prefix of universal and existential variables ordered only partially, so that each existential variable may depend on a chosen subset of the universal ones. Adding such a quantifier to first-order logic expresses properties, such as finiteness of the universe, that first-order logic cannot.

**Definition.** A *Henkin quantifier* is a triple $Q = (A, E, D)$ with $A$ and $E$ disjoint finite sets of universal and existential variables and a dependency relation $D \subseteq A \times E$; $y \in E$ *depends on* $x \in A$ if $(x,y) \in D$. For $A = \{x_1, \dots, x_n\}$ and $E = \{y_1, \dots, y_k\}$,

$$
M \models Q\,\varphi(x_1, \dots, x_n, y_1, \dots, y_k)
$$

is true iff there are functions $f_1, \dots, f_k$ on $M$ such that $M \models \forall \bar{x}\, \varphi(\bar{x}, f_1(\bar{x}_1), \dots, f_k(\bar{x}_k))$, where $\bar{x}_i$ lists the universal variables on which $y_i$ depends. For a set $\mathcal{Q}$ of Henkin quantifiers, $L_\sigma(\mathcal{Q})$ is first-order logic with equality over the vocabulary $\sigma$ extended by the quantifiers in $\mathcal{Q}$, and $L_\emptyset(\mathcal{Q})$ is the case of the empty vocabulary (only equality). Such a logic is *decidable* if its set of valid sentences (tautologies) is decidable.

**Special quantifiers.** $\mathsf{H}_n$ has universal variables $x_1, \dots, x_n$ and existential variables $y_1, \dots, y_n$, with $y_i$ depending only on $x_i$. $\mathsf{E}_n$ has universal variables $x_1, x_2$ and existential variables $y_1, \dots, y_n, z_1, \dots, z_n$, with each $y_i$ depending only on $x_1$ and each $z_i$ only on $x_2$. $\mathsf{H}_\omega = \{\mathsf{H}_n\}_{n \geq 2}$, and similarly $\mathsf{E}_\omega$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Ehrenfeucht's sentence $\neg\exists t\, \mathsf{H}_2 xzyw\, ((y = w \leftrightarrow x = z) \wedge t \neq y)$ says that every injection of the universe into itself is onto, that is, the universe is finite. Enderton and Walkoe showed that the logic of all Henkin quantifiers lies strictly between $\Sigma^1_1$ and $\Delta^1_2$ in expressive power. $L_\sigma(\mathsf{H}_2)$ is decidable for monadic $\sigma$ and undecidable for $\sigma$ with one unary function symbol (Krynicki and Lachlan).

## Sources

- K. Zdanowski, "One Henkin quantifier in the empty vocabulary suffices for undecidability", *Fundamenta Informaticae* 164(4):375–386, 2019, doi:10.3233/FI-2019-1774; read as arXiv:1612.07154v1, <https://arxiv.org/abs/1612.07154v1>: Section 2 (Henkin quantifiers, their semantics, the quantifiers $\mathsf{H}_n$ and $\mathsf{E}_n$, and Theorems 1–5) of arXiv:1612.07154v1.
