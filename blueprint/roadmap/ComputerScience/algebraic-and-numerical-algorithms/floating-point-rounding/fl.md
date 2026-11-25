# Round to nearest, ties to even

For a natural number $p$ and an element $x$ of a linearly ordered field with a floor function, let $e = \lfloor \log_2 |x| \rfloor - (p - 1)$ be the exponent of the last place of $x$ at precision $p$, where $\lfloor \log_2 |x| \rfloor$ is the largest integer $n$ with $2^n \le |x|$ for $x \ne 0$ and is $0$ for $x = 0$, and let $\operatorname{rne}$ round to the nearest integer with ties to the even one. The rounding of $x$ to nearest, ties to even, is

$$\mathrm{fl}_p(x) = \operatorname{rne}(x / 2^e) \cdot 2^e:$$

scale $x$ so that its last place is the units digit, round to the nearest integer with ties to even, and scale back. In particular $\mathrm{fl}_p(0) = 0$.
