# FFT linear convolution gives the product coefficients (Princeton sign)

Let $d$ be a
natural number, $N = 2^{d+1}$ and $\omega = e^{-2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$,
write $P_x = \sum_{j < 2^d} x_j X^j$ and $P_y = \sum_{j < 2^d} y_j X^j$, and let
$z \in \mathbb{C}^N$ be the output of the FFT linear convolution of $x$ and $y$ with root $\omega$,
which pads both vectors with zeros to length $N$ and convolves them circularly by FFT. Then for
every $k < N$, the entry $z_k$ is the coefficient of $X^k$ in $P_x P_y$.
