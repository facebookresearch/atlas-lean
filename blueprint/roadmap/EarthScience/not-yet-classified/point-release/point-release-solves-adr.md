# Point-release kernel solves the advection-diffusion-reaction equation

For $D > 0$, $t > 0$ and all real $M$, $k$, $U$, $x$, the kernel $c(t, x) = M e^{-k t} \exp\!\big(-(x - U t)^2/(4 D t)\big) / \sqrt{4 \pi D t}$ satisfies $c_t + U c_x = D c_{xx} - k c$ at $(t, x)$, where each partial derivative is taken with the other variable held fixed.
