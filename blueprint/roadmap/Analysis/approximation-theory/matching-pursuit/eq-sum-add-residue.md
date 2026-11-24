# Matching pursuit decomposition

For every $m$,

$$f = \sum_{n=0}^{m-1} \langle g_n, R^n f\rangle\, g_n + R^m f$$

(Mallat and Zhang 1993, Section III, equation (15)). This telescoping identity holds for arbitrary vectors $g_n$; it says that the first $m$ selected atoms with the coefficients $\langle g_n, R^n f\rangle$ approximate $f$ up to the residue $R^m f$.
