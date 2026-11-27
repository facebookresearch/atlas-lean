# Moving a shared sampling step out of a tape run

Fix a deterministic algorithm $e : M \times \mathrm{Rnd} \to C$, a distribution $p$ on a type $Z$, a family of defaults $d(z)$ and a family of continuations $K(a, n', \rho', z)$ indexed by $z \in Z$. Consider the [tape run](run-tape.md) whose default is "sample $z \leftarrow p$ and return $d(z)$" and whose continuation is "sample $z \leftarrow p$ and return $K(a, n', \rho', z)$". For every oracle algorithm $c$, length $n$ and tape $\rho \in \mathrm{Rnd}^n$, it equals the distribution obtained by sampling $z \leftarrow p$ once and returning the tape run with default $d(z)$ and continuation $K(\cdot, \cdot, \cdot, z)$.

The sampling of $z$ is moved out of **both** exits; the same $z$ serves whichever exit the run takes.
