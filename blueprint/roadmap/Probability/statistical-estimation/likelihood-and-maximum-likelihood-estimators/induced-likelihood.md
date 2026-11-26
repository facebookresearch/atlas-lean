# Induced likelihood

Let $F$ be a normalized density family on $\Omega$ with parameter
set $\Theta$, let $n$ be a sample size, let $\tau : \Theta \to H$ be a map into a set $H$, and
let $x \in \Omega^n$ be a sample. For $\eta$ in the image of $\tau$, the induced likelihood of
$\eta$ at $x$ is the supremum, in $[0, \infty]$, of the iid likelihood $L_n(\theta; x)$ over
the fiber of $\tau$ above $\eta$:

$$L^*_n(\eta; x) = \sup_{\theta \in \Theta,\ \tau(\theta) = \eta} L_n(\theta; x).$$

Since $\eta$ lies in the image of $\tau$, the fiber is nonempty; no inverse of $\tau$ is
chosen.
