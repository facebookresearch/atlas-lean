# Iterates that lower a depth by one

Let $f \colon \alpha \to \alpha$ and $d \colon \alpha \to \mathbb{N}$ satisfy $d(f(x)) + 1 = d(x)$ for every $x$ with $f(x) \ne x$. If $f^{k}(x) = y$ for some $k \in \mathbb{N}$, then

$$f^{\,d(x) - d(y)}(x) = y,$$

where $d(x) - d(y)$ is truncated subtraction on $\mathbb{N}$. Thus $y$ is reached from $x$ after exactly $d(x) - d(y)$ steps.
