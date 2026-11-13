# Watson's inverse factorial expansion

Let $A,B,\rho,\sigma,\alpha,\delta>0$, $\gamma\ge 0$
and $p$ be real numbers with $\alpha+3\delta\lt \pi/2$ and $1\lt p<1+e^{-\pi\cot\alpha}$. Let $S$ be the
sector $\{z\in\mathbb{C} : |z|>\gamma,\ |\arg z|\le\pi/2+\alpha+3\delta\}$, where $\arg$ is the
principal argument. Let $f$ be a complex function that is analytic at every point of the
half-plane $\{z : \mathrm{Re}\,z>0\}$ and at every point of $S$, let $a_0,a_1,\dots$ be complex
numbers with $|a_n|\lt A\rho^n n!$ for every $n\ge 0$, and let $R_0,R_1,\dots$ be complex functions
such that for every $n\ge 0$ and every $z\in S$

$$f(z)=\sum_{k=0}^{n}\frac{a_k}{z^k}+R_n(z)\qquad\text{and}\qquad|R_n(z)\,z^{n+1}|\lt B\sigma^n n!.$$

Suppose that $M_0$ is the largest real $x>0$ with

$$e^{-2\cos\alpha/(\rho x)}-2\cos\big(\sin\alpha/(\rho x)\big)e^{-\cos\alpha/(\rho x)}+1-p^2=0.$$

Then for every real $M$ with $0\lt M\le M_0$ and every complex $w$ with $\mathrm{Re}\,w\ge 0$ there
are complex numbers $b_0,b_1,\dots$ such that for every $z$ with $\mathrm{Re}\,z>0$ the series

$$\sum_{k=1}^{\infty}\frac{b_k}{(Mz+w+1)(Mz+w+2)\cdots(Mz+w+k)}$$

converges absolutely and its sum is $f(z)-b_0$.

## Sources

- https://cs.uwaterloo.ca/journals/JIS/VOL25/Schumacher/schu9.tex, lines 370-417. Scope exclusion: excludes the `M = 1, w = 0` specialization and the later Stirling-coefficient theorem.
