# Target collision resistance

Let $K$, $X$, $Y$ and $R$ be families of types indexed by the security parameter $n$, with decidable equality on $X_n$ and $Y_n$, and $X_n$ and $R_n$ nonempty for every $n$. Let $H_n$ be a keyed hash function with keys in $K_n$, inputs in $X_n$ and outputs in $Y_n$, and let a class of admissible families of [target-collision adversaries](tcradversary.md) $A_n$ with coins in $R_n$ be given. The family $H$ is **target collision resistant** (universal one-way, after Naor and Yung) relative to that class when, **for every admissible family** $A$, the sequence

$$
n \mapsto \mathrm{tcrAdv}(H_n, A_n)
$$

is a negligible advantage. A real sequence $\varepsilon$ is a negligible advantage when $\varepsilon(n) \le e(n)$ for all $n$ for some $e : \mathbb{N} \to \mathbb{Q}$ with: for every $c$ there is $N$ such that $e(n) \le 1/n^c$ for all $n \ge N$. The nonemptiness hypotheses make adversaries exist ([a target-collision adversary exists](nonempty-2.md)); without them the notion would hold vacuously.
