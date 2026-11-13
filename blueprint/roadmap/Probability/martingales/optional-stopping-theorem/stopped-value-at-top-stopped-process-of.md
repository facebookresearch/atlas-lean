# Stopping at a later time does not change the stopped value

Let $(f_n)_{n \in \mathbb{N}}$
be a sequence of real-valued functions on $\Omega$ and let
$L, M : \Omega \to \mathbb{N} \cup \{\infty\}$ satisfy $L(\omega) \le M(\omega)$ for every
$\omega$. Then the value at $L$ of the stopped process $n \mapsto f_{M \wedge n}$ equals the value
$f_L$ of $f$ at $L$ at every point of $\Omega$. Here the value of a sequence $(g_n)$ at a point
$\omega$ where the time is infinite is $\lim_n g_n(\omega)$ when this limit exists, and otherwise
a fixed default value that depends only on the sequence $(g_n(\omega))_{n \in \mathbb{N}}$.

On $\{L = \infty\}$ the inequality forces $M = \infty$, so there the stopped process is $f$
itself.
