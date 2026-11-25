# Soft thresholding

For real numbers $t$ and $z$, the soft thresholding of $z$ at $t$ is
$S_t(z) = z - t$ if $z > t$; otherwise $S_t(z) = z + t$ if $z < -t$; and $S_t(z) = 0$ in the
remaining case.

For $t \ge 0$ this shrinks $z$ towards $0$ by $t$ and sets it to $0$ when $|z| \le t$.
