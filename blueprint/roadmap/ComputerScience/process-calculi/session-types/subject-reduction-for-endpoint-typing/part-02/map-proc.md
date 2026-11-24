# Capture-safe renaming of processes

Let $f$ be a map from names to names. The renaming $f(p)$ of a process $p$ is defined by recursion:
$f(\mathbf{0}) = \mathbf{0}$, $f(\overline{a}\langle b\rangle.p) = \overline{f(a)}\langle
f(b)\rangle.f(p)$, $f(a(\cdot).p) = f(a)(\cdot).f^{\uparrow}(p)$, $f(p \mid q) = f(p) \mid f(q)$,
$f(\nu\,p) = \nu\,f^{\uparrow}(p)$, $f(!p) = {!f(p)}$ and $f(p + q) = f(p) + f(q)$, where
$f^{\uparrow}$ is the extension of $f$ under one binder (fixing $\mathrm{v}_0$ and shifting the
images of outer names).
