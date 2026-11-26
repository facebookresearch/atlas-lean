# Invariant maps descend uniquely to the quotient tower

Let $\mathcal{O}$ be a commutative ring, $\pi \in \mathcal{O}$, and let $(X_n)$ be a tower of schemes over $\operatorname{Spec} \mathcal{O}/(\pi^{n+1})$ with transition morphisms $x^t_n : X_n \to X_{n+1}$ and group actions $a_n : G \to \operatorname{Aut}(X_n)$ of a group $G$. Let $D$ be a quotient datum for these data, with quotient tower $(Y_n)$ and quotient morphisms $p_n : X_n \to Y_n$. Let $T$ be a scheme and $w_n : X_n \to T$ morphisms that are $G$-invariant, $w_n \circ a_n(g) = w_n$ for all $n$ and $g \in G$, and compatible with the transitions, $w_{n+1} \circ x^t_n = w_n$ for all $n$. Then there is a unique family of morphisms $u_n : Y_n \to T$ with

$$
u_n \circ p_n = w_n \quad \text{for all } n \in \mathbb{N}.
$$
