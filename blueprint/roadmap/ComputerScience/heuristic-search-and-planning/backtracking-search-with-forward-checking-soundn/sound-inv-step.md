# Sound Inv step

If the soundness invariant holds for the input domains, the current domains and the current assignment, and $a$ lies in the current domain of $x$ and is compatible with itself ($x = a$ paired with $x = a$ is allowed), then assigning $x = a$ and applying forward checking keeps the invariant. Without self-compatibility the step can break the invariant: a single variable with domain $\{a\}$ and a self-loop forbidding $(a, a)$.
