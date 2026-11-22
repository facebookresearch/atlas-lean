# Value of a process at a possibly infinite time

For a real-valued process
$(f_n)_{n \in \mathbb{N}}$ on $\Omega$ and a map $\tau : \Omega \to \mathbb{N} \cup \{\infty\}$,
the value $f_\tau$ of $f$ at $\tau$ is the function on $\Omega$ given by
$f_\tau(\omega) = f_{\tau(\omega)}(\omega)$ when $\tau(\omega) < \infty$ and
$f_\tau(\omega) = \lim_{n \to \infty} f_n(\omega)$ when $\tau(\omega) = \infty$, where the limit
is an unspecified real number if $(f_n(\omega))_n$ does not converge.

Unlike the usual stopped value, which uses an arbitrary finite index where $\tau = \infty$,
this uses the limit there, as the general optional stopping theorem requires.
