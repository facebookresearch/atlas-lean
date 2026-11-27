# The rounding error at the scale of the last place

Let $x$ be an element of a linearly ordered field with a floor function, let $p$ be a natural number, and let $e = \lfloor \log_2 |x| \rfloor - (p - 1)$ be the exponent of the last place of $x$ at precision $p$, where $\lfloor \log_2 |x| \rfloor$ is the largest integer $n$ with $2^n \le |x|$ for $x \ne 0$ and is $0$ for $x = 0$. Writing $\operatorname{rne}$ for rounding to the nearest integer with ties to even, the rounding $\mathrm{fl}_p(x) = \operatorname{rne}(x / 2^e) \cdot 2^e$ of $x$ to nearest, ties to even, at precision $p$ has the error

$$\mathrm{fl}_p(x) - x = \big(\operatorname{rne}(x / 2^e) - x / 2^e\big) \cdot 2^e.$$
