# Alicki-Fannes-Winter continuity of conditional entropy (classical case)

Let $h_2(x) = -x\log_2 x - (1-x)\log_2(1-x)$ be the binary entropy in bits. Let $P, Q$ be joint laws of $(Y, X)$ on finite sets $\beta \times \alpha$ with statistical distance $\delta(P, Q) \le \varepsilon \le 1$. Then

$$
\big|H(X\mid Y)_P - H(X\mid Y)_Q\big| \le \varepsilon \log_2|\alpha| + (1+\varepsilon)\, h_2\Big(\frac{\varepsilon}{1+\varepsilon}\Big),
$$

a bound independent of $|\beta|$. Consequently $H(X\mid Y)_Q \ge t$ implies $H(X\mid Y)_P \ge t - \varepsilon\log_2|\alpha| - (1+\varepsilon)h_2(\varepsilon/(1+\varepsilon))$, and for joint laws of $(C, A, B)$ at distance at most $\varepsilon$, $|I(A;B\mid C)_P - I(A;B\mid C)_Q| \le \varepsilon\log_2|A| + 2(1+\varepsilon)h_2(\varepsilon/(1+\varepsilon))$.

## Proof sketch

With $d = \delta(P,Q)$, write $P + d\Delta^- = Q + d\Delta^+$ where $\Delta^\pm$ are the normalized positive and negative parts of $P - Q$, and view both sides as the mixture $\Omega$ with weights $\frac{1}{1+d}, \frac{d}{1+d}$. Concavity and the mixture bound for conditional entropy applied to both decompositions of $\Omega$ give $(1+d)^{-1}|H_P - H_Q| \le \frac{d}{1+d}\log_2|\alpha| + h_2(d/(1+d))$. Monotonicity of the modulus on $[0,1]$ passes from $d$ to $\varepsilon$; for mutual information write $I(A;B\mid C) = H(A\mid C) - H(A\mid C,B)$ and apply the same decomposition to both terms with the same $\Delta^\pm$: the main terms combine into $d\,(I(A;B\mid C)_{\Delta^+} - I(A;B\mid C)_{\Delta^-})$, at most $d\log_2|A|$ in absolute value, while the two binary-entropy terms add.

## Depends on

- [Conditional entropy of a finite joint law](../conditional-entropy-and-mutual-information/finite-conditional-entropy.md)
- [Conditional mutual information of a finite joint law](../conditional-mutual-information/finite-conditional-mutual-information.md)

## Proof depends on

- [Concavity of conditional entropy and the mixture bound](concavity-of-conditional-entropy.md)

## Sources

- A. Winter, "Tight Uniform Continuity Bounds for Quantum Entropies: Conditional Entropy, Relative Entropy Distance and Energy Constraints", Communications in Mathematical Physics 347, 2016.
- J. Januzelli, M. Rosulek and L. Roy, "Lower Bounds for Garbled Circuits from Shannon-Type Information Inequalities", Advances in Cryptology (CRYPTO 2025), 2025.
