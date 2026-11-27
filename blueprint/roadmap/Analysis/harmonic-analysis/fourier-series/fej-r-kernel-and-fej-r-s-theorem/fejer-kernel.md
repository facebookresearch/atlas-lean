# The Fejér kernel

Let $T > 0$ and, for $n \in \mathbb{Z}$, let
$e_n(x) = e^{2\pi i n x / T}$ be the $n$-th Fourier character on the circle
$\mathbb{R}/T\mathbb{Z}$. For a natural number $N$, the $N$-th Fejér kernel is the function
$K_N : \mathbb{R}/T\mathbb{Z} \to \mathbb{C}$ given by the Cesàro mean of the Dirichlet kernels,
$K_N(x) = \frac{1}{N+1} \sum_{k=0}^{N} \sum_{n=-k}^{k} e_n(x)$.

Writing $x$ also for a real representative, when $\sin(\pi x / T) \ne 0$ the kernel has the closed
form $K_N(x) = \frac{1}{N+1} \left(\frac{\sin((N+1)\pi x / T)}{\sin(\pi x / T)}\right)^2$.
This normalization is for the Haar probability measure on $\mathbb{R}/T\mathbb{Z}$; for $T = 2\pi$,
the kernel for integration against Lebesgue measure is $K_N / (2\pi)$.
