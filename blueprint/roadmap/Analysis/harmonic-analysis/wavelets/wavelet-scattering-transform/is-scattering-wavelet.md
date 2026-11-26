# Scattering wavelet in dimension one

The standing assumptions on the wavelet $\psi$ and the low-pass function $\varphi$ in Section 2.1 of S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), 1331–1398 (arXiv:1101.2286), in dimension $d = 1$ with $G = \{1, -1\}$ and real-valued signals:
- $\hat\psi$ is real, and $\hat\varphi$ is real and symmetric;
- $\psi$ and $\varphi$ are twice continuously differentiable, and they and their first and second derivatives are $O((1 + |x|)^{-3})$, that is $O((1 + |x|)^{-d-2})$;
- the Littlewood–Paley condition (9) with $\beta = 1/2$ holds for almost every $\omega$:

$$\tfrac12 \sum_{j \in \mathbb{Z}} \big(|\hat\psi(2^{-j}\omega)|^2 + |\hat\psi(-2^{-j}\omega)|^2\big) = 1, \qquad |\hat\varphi(\omega)|^2 = \tfrac12 \sum_{j \le 0} \big(|\hat\psi(2^{-j}\omega)|^2 + |\hat\psi(-2^{-j}\omega)|^2\big).$$

By Proposition 2.1 this makes the wavelet transform $W_J f = (A_J f, (f \star \psi_{2^j})_{2^j > 2^{-J}})$ unitary on real-valued functions of $L^2(\mathbb{R})$.
