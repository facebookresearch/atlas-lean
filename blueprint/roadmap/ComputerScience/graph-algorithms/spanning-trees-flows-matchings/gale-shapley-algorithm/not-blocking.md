# A stable matching has no blocking pair

Let each proposer $m$ have a ranking $\sigma_m$ of
the $n$ receivers and each receiver $w$ a ranking $\tau_w$ of the $n$ proposers, where
$\sigma_m^{-1}(x)$ and $\tau_w^{-1}(x)$ are ranks ($0$ the best). If $\nu$ is a perfect matching
that is stable for the preferences given by these rankings, there are no proposer $m$ and
receiver $w$ with $\sigma_m^{-1}(w) < \sigma_m^{-1}(\nu(m))$ and
$\tau_w^{-1}(m) < \tau_w^{-1}(\nu^{-1}(w))$.
