# Filtrations and stopping times

Let $(\Omega,\mathcal A,P)$ be a probability space and $\iota$ a preordered index set. A filtration is a family $(\mathcal F_i)_{i\in\iota}$ of sub-$\sigma$-algebras of $\mathcal A$ with $\mathcal F_i\subseteq\mathcal F_j$ whenever $i\le j$. For processes $X=(X_i)_{i\in\iota}$ with values in a measurable space:

- $X$ is adapted if each $X_i$ is $\mathcal F_i$-measurable; for values in a normed space, strongly adapted means each $X_i$ is $\mathcal F_i$-strongly measurable.
- When $\iota$ carries a topology and Borel $\sigma$-algebra, $X$ is progressive if for every $i$ the map $(j,\omega)\mapsto X_j(\omega)$ on $\{j\in\iota:j\le i\}\times\Omega$ is measurable for the product of the Borel $\sigma$-algebra and $\mathcal F_i$.
- A stopping time is a map $\tau:\Omega\to\iota\cup\{\infty\}$ with $\{\tau\le i\}\in\mathcal F_i$ for every $i\in\iota$.
- For a stopping time $\tau$ with values in $\iota$, the stopped value is $X_\tau(\omega)=X_{\tau(\omega)}(\omega)$; for a linearly ordered index set, the stopped process is $X^\tau_i=X_{\min(i,\tau)}$.
- For a linearly ordered index set, the right-continuous version of the filtration is $\mathcal F_{i+}=\bigcap_{j>i}\mathcal F_j$; the filtration is right-continuous if $\mathcal F_{i+}=\mathcal F_i$ for all $i$.

For $\iota=\mathbb N$ (or any countable well-ordered index set), a process $u$ and a measurable set $s$, the hitting time after $n$ is $\inf\{i\ge n:u_i\in s\}$, with value $\infty$ if there is no such $i$, and the hitting time between $n$ and $m$ is $\inf\{i\in[n,m]:u_i\in s\}$, with value $m$ if there is no such $i$. If $u$ is adapted, both are stopping times. For uncountable index sets the measurability of hitting times needs extra regularity of paths or of the filtration.

## Expansion

A full page proves that the hitting times above are stopping times for a countable index set, that constant times and minima and maxima of two stopping times are stopping times, and that stopped values of adapted processes at stopping times with countably many values are $\mathcal F_\tau$-measurable, where $\mathcal F_\tau=\{A\in\mathcal A:A\cap\{\tau\le i\}\in\mathcal F_i\text{ for all }i\}$. It should establish that the absorption time $\inf\{n:Y_n\in\{0,M\}\}$ of a Markov chain $Y$ on $\{0,\dots,M\}$ is a stopping time for the natural filtration of $Y$.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer, 1991, <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Ch. 1, filtrations and stopping times.
