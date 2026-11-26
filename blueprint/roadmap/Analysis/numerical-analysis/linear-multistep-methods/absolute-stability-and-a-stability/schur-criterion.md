# Schur's criterion

Let $\varphi(r) = c_k r^k + \dots + c_1 r + c_0$ be a polynomial with complex coefficients, $c_k \ne 0$ and $c_0 \ne 0$. It is a *Schur polynomial* if each of its roots $r_s$ satisfies $|r_s| < 1$. Let

$$\hat\varphi(r) = \bar c_0 r^k + \bar c_1 r^{k-1} + \dots + \bar c_{k-1} r + \bar c_k, \qquad \varphi_1(r) = \frac{1}{r}\big[\hat\varphi(0)\varphi(r) - \varphi(0)\hat\varphi(r)\big],$$

a polynomial of degree at most $k - 1$. Then $\varphi$ is a Schur polynomial if and only if $|\hat\varphi(0)| > |\varphi(0)|$ and $\varphi_1$ is a Schur polynomial.

Applied recursively to the stability polynomial $\pi(r; \bar h) = \rho(r) - \bar h \sigma(r)$, it decides whether a linear multistep method is [absolutely stable](absolute-stability.md) for $\bar h$.

## Related topics

- [Routh–Hurwitz criterion](routh-hurwitz-criterion.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.7.1, Theorem 14 (Schur's criterion, stated without proof there) and Exercise 4. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
