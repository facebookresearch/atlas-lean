# The uniform deviation of an empirical distribution function is a supremum over the rationals

For a sample $x_1, \dots, x_n$ of real numbers write $F_n(t) = \#\{i : x_i \le t\}/n$ for its empirical distribution function (with $F_n \equiv 0$ when $n = 0$). Let $F : \mathbb{R} \to \mathbb{R}$ be right-continuous at every point, and suppose $|F_n(x) - F(x)| \le C$ for all $x$ and some constant $C$. Then

$$\sup_{x \in \mathbb{R}} |F_n(x) - F(x)| = \sup_{q \in \mathbb{Q}} |F_n(q) - F(q)|.$$

This is the case $f = F_n$, $g = F$ of the corresponding statement for two right-continuous functions.
