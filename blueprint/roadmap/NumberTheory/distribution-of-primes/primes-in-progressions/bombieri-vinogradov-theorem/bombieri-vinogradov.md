# Bombieri–Vinogradov theorem

Let $\psi(y; q, a)$ denote Chebyshev's function in the
residue class of $a$ modulo $q$, and let $\varphi$ be Euler's totient function. For a natural
number $x$ and a real number $A$, let $S(x, A)$ be the sum, over the integers $q$ with
$1 \le q \le x$ and $q \le \sqrt{x} / (\log x)^{A + 5}$, of the maximum of
$\left|\psi(y; q, a) - y/\varphi(q)\right|$ over the natural numbers $y \le x$ and $a < q$
coprime to $q$. Then for every real number $A > 0$ there are a real number $C > 0$ and a natural
number $x_0$ such that every natural number $x \ge x_0$ satisfies $S(x, A) \le C x / (\log x)^A$.

The main term $y/\varphi(q)$ depends on the inner variable $y$; it is not a
logarithmic-integral term depending on $x$.

## Sources

- S. Baier and L. Zhao, *Bombieri-Vinogradov Type Theorem for Sparse Sets of Moduli*, arXiv:math/0602116, classical theorem display (1.1), source lines 54–62. The official source bundle has SHA-256 `86b591e2c1c73eadc18774d32318421b8f12a99ab89cc213a3f54aa7953da00f`, the TeX file has SHA-256 `0826f6d0f8b5f5be49c6238fcdda2bb65d1b1b81a74c964a4328cb5454d0bdb4`, the exact newline-terminated span has SHA-256 `0c8e89016584b4acbcc9a1c8fd12cb988749e827143e6e83c0e2c4cc025dff0a`, and the semantic id is `jis_grounded_f3db17ecd03ec2208fa68754`.
