# Schur's criterion

Call a nonzero polynomial with complex coefficients a *Schur polynomial* if each of its roots $r_s$ satisfies $|r_s| < 1$; a nonzero constant is a Schur polynomial. Let $\varphi(r) = c_k r^k + \dots + c_1 r + c_0$ with $k \ge 1$ and $c_k \ne 0$ ($c_0 = 0$ is allowed), and let

$$\hat\varphi(r) = \bar c_0 r^k + \bar c_1 r^{k-1} + \dots + \bar c_{k-1} r + \bar c_k, \qquad \varphi_1(r) = \frac{1}{r}\big[\hat\varphi(0)\varphi(r) - \varphi(0)\hat\varphi(r)\big],$$

a polynomial of degree at most $k - 1$. Then $\varphi$ is a Schur polynomial if and only if $|\hat\varphi(0)| > |\varphi(0)|$ and $\varphi_1$ is a Schur polynomial. When $|\hat\varphi(0)| > |\varphi(0)|$, the leading coefficient of $\varphi_1$ is $|c_k|^2 - |c_0|^2 > 0$, so $\varphi_1$ has degree exactly $k - 1$ and the test recurses down to a nonzero constant. When $c_0 = 0$, $\varphi_1 = \bar c_k \varphi(r)/r$, so the test strips the root $0$.

To decide whether a linear multistep method is [absolutely stable](absolute-stability.md) for $\bar h$, first check that the stability polynomial $\pi(r; \bar h) = \rho(r) - \bar h \sigma(r)$ has degree $k$ (otherwise it is not), then apply the test recursively to it. For example, explicit Euler at $\bar h = -1$ gives $\pi(r) = r$ and $\pi_1 = 1$, a Schur polynomial.

## Depends on

- [Absolute stability of a linear multistep method](absolute-stability.md)

## Related topics

- [Routh–Hurwitz criterion](routh-hurwitz-criterion.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.7.1, Theorem 14 (Schur's criterion, stated without proof there) and Exercise 4. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
