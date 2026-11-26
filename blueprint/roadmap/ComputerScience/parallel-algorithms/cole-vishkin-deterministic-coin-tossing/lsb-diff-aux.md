# Bounded search for the lowest differing bit

For natural numbers $f$, $x$ and $y$, the value $d_f(x, y)$ is defined by recursion on the bound $f$: $d_0(x, y) = 0$, and $d_{f+1}(x, y) = d_f(\lfloor x/2 \rfloor, \lfloor y/2 \rfloor) + 1$ if the lowest binary digits of $x$ and $y$ agree, and $d_{f+1}(x, y) = 0$ otherwise. So $d_f(x, y)$ is the lowest bit position at which $x$ and $y$ differ when that position is below $f$, and it equals $f$ when the lowest $f$ binary digits of $x$ and $y$ all agree.
