# Log multivariate Gaussian PDFReal div

Let $\iota$ be a finite index set with $n = \lvert \iota \rvert$, and let $S, T$ be positive definite real $\iota \times \iota$ matrices. For $m \in \mathbb{R}^{\iota}$ let

$$p_{m,S}(x) = \frac{1}{(2\pi)^{n/2} \sqrt{\det S}} \exp\left(-\frac{(x - m)^{\top} S^{-1} (x - m)}{2}\right)$$

be the Gaussian density. Then for all $m, q, x \in \mathbb{R}^{\iota}$,

$$\log\frac{p_{m,S}(x)}{p_{q,T}(x)} = \frac{1}{2}\left(\log\frac{\det T}{\det S} - (x - m)^{\top} S^{-1} (x - m) + (x - q)^{\top} T^{-1} (x - q)\right)$$
