# Bounded optional stopping, conditional form, supermartingale dual

Let $\mu$ be a
measure on a measurable space $\Omega$, let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration
such that $\mu$ is σ-finite on every $\mathcal{F}_n$, and let $(f_n)_{n \in \mathbb{N}}$ be a
real-valued supermartingale with respect to $(\mathcal{F}_n)$ and $\mu$. Let $L$ and $M$ be
stopping times with values in $\mathbb{N} \cup \{\infty\}$ such that
$L(\omega) \le M(\omega) \le N$ for every $\omega$, for some $N \in \mathbb{N}$, and suppose
that $\mu$ is σ-finite on the σ-algebra $\mathcal{F}_L$ of events $A$ with
$A \cap \{L \le n\} \in \mathcal{F}_n$ for every $n$. Write $f_L(\omega) = f_{L(\omega)}(\omega)$
and $f_M(\omega) = f_{M(\omega)}(\omega)$ for the stopped values. Then
$\mathbb{E}_\mu[f_M \mid \mathcal{F}_L] \le f_L$ holds $\mu$-almost everywhere.

This follows from the submartingale version applied to $-f$.
