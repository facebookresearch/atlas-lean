# Energy conservation of matching pursuit

If every $g_n$ is a unit vector, then for every $m$,

$$\|f\|^2 = \sum_{n=0}^{m-1} |\langle g_n, R^n f\rangle|^2 + \|R^m f\|^2$$

(Mallat and Zhang, *Matching pursuits with time-frequency dictionaries*, IEEE Trans. Signal Process. 41 (1993), Section III, equation (17)). Although the decomposition is nonlinear, it conserves energy as an orthogonal expansion would, whatever atoms are selected. In particular $\sum_n |\langle g_n, R^n f\rangle|^2 \le \|f\|^2$ converges and $\|R^m f\|$ decreases to a limit.
