# Discrete-logarithm experiment with Pedersen parameters

The experiment draws $h$ by Pedersen parameter generation (as $g^x$ for a uniform unit $x$ of
$\mathbb{Z}/q$, the same distribution as in the binding experiment) and the adversary's coins, and
outputs $1$ when the adversary's exponent $x'$ satisfies $g^{x'} = h$. Unlike Katz and Lindell's
experiment (Section 8.3.2), which draws $h$ uniformly from $G$, it never draws $h = 1$ when $q$ is
prime, $g^q = 1$ and $g \neq 1$.
