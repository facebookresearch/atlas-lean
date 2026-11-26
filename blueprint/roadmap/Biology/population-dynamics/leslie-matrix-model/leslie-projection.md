# Population after t steps of the Leslie model

For $n$ age classes with real fertilities $f_0, \dots, f_{n-1}$ and real survival coefficients
$s_0, \dots, s_{n-1}$, let $L$ be the [Leslie matrix](leslie-matrix.md), and let
$x_0, x_1, \dots \in \mathbb{R}^n$ satisfy $x_{t+1} = L x_t$ for every $t \in \mathbb{N}$. Then
$x_t = L^t x_0$ for every $t \in \mathbb{N}$. No sign condition on the coefficients is needed, and
nothing is claimed about convergence.
