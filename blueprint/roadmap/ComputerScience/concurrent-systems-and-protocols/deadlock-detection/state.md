# Resource-allocation state

For a type $P$ of processes and a type $R$ of resource types,
a state consists of two functions $\mathrm{alloc}, \mathrm{request} : P \to R \to \mathbb{N}$:
$\mathrm{alloc}(p)(r)$ is the number of instances of resource type $r$ that process $p$ holds,
and $\mathrm{request}(p)(r)$ is the number of instances of $r$ that $p$ is waiting for.
