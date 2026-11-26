# Conditional entropy in one coordinate

Let $E$ be a finite set, $p$ a real number, $g : \{0, 1\}^E \to \mathbb{R}$, $e \in E$ and $\omega \in \{0, 1\}^E$. With [$\Phi(x) = x \log x$](esd-phi.md), the logarithm being extended by $\log 0 = 0$ and $\log x = \log \lvert x\rvert$ for $x < 0$, the conditional entropy of $g$ in coordinate $e$ at $\omega$ is

$$\mathrm{Ent}_e(g)(\omega) = p\, \Phi\big(g(\omega^{e \to 1})\big) + (1-p)\, \Phi\big(g(\omega^{e \to 0})\big) - \Phi\big(p\, g(\omega^{e \to 1}) + (1-p)\, g(\omega^{e \to 0})\big),$$

where $\omega^{e \to b}$ agrees with $\omega$ except that its coordinate $e$ is $b$; it depends only on the coordinates of $\omega$ other than $e$.
