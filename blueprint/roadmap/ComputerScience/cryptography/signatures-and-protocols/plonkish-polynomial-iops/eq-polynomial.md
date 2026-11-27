# The multilinear equality polynomial on the Boolean hypercube

For $s\ge 1$ and a field $\mathbb{F}$, the *equality polynomial* is

$$
\widetilde{\mathrm{eq}}(x,y)=\prod_{i=1}^{s}\bigl(x_iy_i+(1-x_i)(1-y_i)\bigr)\in\mathbb{F}[x_1,\dots,x_s,y_1,\dots,y_s].
$$

It is multilinear in each block of variables, and for $x,y\in\{0,1\}^{s}$ it equals $1$ if $x=y$ and $0$ otherwise. Consequently, for any $f:\{0,1\}^{s}\to\mathbb{F}$ with multilinear extension $\widetilde{f}$ and any $r\in\mathbb{F}^{s}$, $\widetilde{f}(r)=\sum_{b\in\{0,1\}^{s}}\widetilde{\mathrm{eq}}(r,b)f(b)$, and the $2^{s}$ values $\widetilde{\mathrm{eq}}(r,b)$ can be computed with $O(2^{s})$ field operations.

## Depends on

- [Multilinear extension of a Boolean function](../../../../TheoryOfComputation/hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Sources

- Srinath Setty, "Spartan: Efficient and General-Purpose zkSNARKs without Trusted Setup", CRYPTO (2020), IACR ePrint 2019/550.
- Binyi Chen, Benedikt Bünz, Dan Boneh, Zhenfei Zhang, "HyperPlonk: Plonk with Linear-Time Prover and High-Degree Custom Gates", EUROCRYPT (2023), IACR ePrint 2022/1355.
