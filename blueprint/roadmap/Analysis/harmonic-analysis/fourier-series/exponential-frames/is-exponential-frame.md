# Frames of exponentials

For a set $A \subseteq \mathbb{R}$ and a set $\Lambda \subseteq \mathbb{R}$ of frequencies, the exponentials $t \mapsto e^{i\lambda t}$, $\lambda \in \Lambda$, form a frame in $L^2(A)$ when there are real constants $0 < a \le b$ such that

$$a \int_A |f(t)|^2\,dt \;\le\; \sum_{\lambda \in \Lambda} \Bigl| \int_A f(t)\, e^{-i\lambda t}\,dt \Bigr|^2 \;\le\; b \int_A |f(t)|^2\,dt$$

for every complex-valued $f \in L^2(A)$, the sum being taken in $[0, \infty]$.

The inner integral is a Lebesgue (Bochner) integral, read as $0$ when $f(t)\,e^{-i\lambda t}$ is not integrable on $A$. When $A$ has finite measure, every $f \in L^2(A)$ is integrable on $A$, each exponential lies in $L^2(A)$, and the inner integral is the $L^2(A)$ inner product $\langle f, e_\lambda \rangle$ with $e_\lambda(t) = e^{i\lambda t}$; the inequalities are then the usual frame inequalities. Only this case enters [Führ's question](open-dense-exponential-frame.md). For an arbitrary $A$ the definition keeps the raw inequalities above, which need not be inner products: on $A = \mathbb{R}$ no exponential lies in $L^2(\mathbb{R})$, and $f(t) = (1 + |t|)^{-1}$ is square-integrable while $\int_{\mathbb{R}} f(t)\,dt$ diverges.
