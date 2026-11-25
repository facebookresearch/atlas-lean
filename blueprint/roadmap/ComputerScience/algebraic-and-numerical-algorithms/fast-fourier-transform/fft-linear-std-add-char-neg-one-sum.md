# FFT linear convolution computes the convolution sums (Princeton sign)

Let $d$ be a
natural number, $N = 2^{d+1}$ and $\omega = e^{-2\pi i/N}$. For vectors $x, y \in \mathbb{C}^{2^d}$,
extended by $x_j = y_j = 0$ for $j \ge 2^d$, let $z \in \mathbb{C}^N$ be the output of the FFT
linear convolution of $x$ and $y$ with root $\omega$, which pads both vectors with zeros to length
$N$ and convolves them circularly by FFT. Then for every $k < N$,

$$z_k = \sum_{j=0}^{k} x_j \, y_{k-j}.$$
