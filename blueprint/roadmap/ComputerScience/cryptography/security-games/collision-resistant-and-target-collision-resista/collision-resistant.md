# Collision resistance

Let $K$, $X$, $Y$ and $R$ be families of types indexed by the security parameter $n$, with decidable equality on $X_n$ and $Y_n$, and $X_n$ and $R_n$ nonempty for every $n$. Let $H_n$ be a keyed hash function with keys in $K_n$, inputs in $X_n$ and outputs in $Y_n$, and let a class of admissible families of [collision finders](collision-finder.md) $A_n$ with coins in $R_n$ be given. The family $H$ is **collision resistant** relative to that class (Katz and Lindell, Definition 5.2) when, **for every admissible family** $A$, the sequence

$$
n \mapsto \mathrm{collAdv}(H_n, A_n)
$$

is a negligible advantage. A real sequence $\varepsilon$ is a negligible advantage when $\varepsilon(n) \le e(n)$ for all $n$ for some $e : \mathbb{N} \to \mathbb{Q}$ with: for every $c$ there is $N$ such that $e(n) \le 1/n^c$ for all $n \ge N$.

A finder makes no oracle queries, so the admissible class is a parameter (in the textbook, probabilistic polynomial time); with the class of all families this is security against unbounded finders. The nonemptiness hypotheses make finders exist ([a collision finder exists](nonempty.md)); without them the notion would hold vacuously. No efficiency or compression condition is imposed on $H$, so an injective family is collision resistant.
