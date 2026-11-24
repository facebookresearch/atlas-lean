# Standard Grover iteration count

Let $M$ be a set of marked elements of a finite search
space of size $N$, and let $\theta = \arcsin \sqrt{|M| / N}$ be its Grover angle. The standard
iteration count is $\lfloor \pi / (4\theta) \rfloor$, the largest natural number at most
$\pi / (4\theta)$; it is $0$ when $\theta = 0$, that is, when no element is marked.
