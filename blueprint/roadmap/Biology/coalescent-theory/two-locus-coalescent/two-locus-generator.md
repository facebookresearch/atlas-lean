# Generator of the two-locus Wright–Fisher diffusion

For real numbers $\rho$ and $\nu$, the operator $L_{\rho,\nu}$ on real polynomials $f$ in the four gamete frequencies $x_g$, $g \in \{AB, Ab, aB, ab\}$, given by

$$L_{\rho,\nu} f = \frac{1}{2} \sum_{g, h} x_g (\delta_{gh} - x_h)\, \partial_g \partial_h f + \sum_g \Bigl(-\frac{\rho}{2}\, \varepsilon_g D + \nu\,(x_{g'} + x_{g''} - 2 x_g)\Bigr) \partial_g f,$$

where $D = x_{AB} x_{ab} - x_{Ab} x_{aB}$, $\varepsilon_g = 1$ for the coupling gametes $AB$ and $ab$ and $\varepsilon_g = -1$ for $Ab$ and $aB$, and $g'$, $g''$ are the gametes obtained from $g$ by changing the allele at the first, respectively the second, locus. For $\rho, \nu \ge 0$ it is the generator of the two-locus Wright–Fisher diffusion with time in units of $2N$ generations, $\rho = 4Nr$, and symmetric mutation at rate $\nu$ per locus in each direction ($\nu = \theta/2$, $\theta = 4Nu$).
