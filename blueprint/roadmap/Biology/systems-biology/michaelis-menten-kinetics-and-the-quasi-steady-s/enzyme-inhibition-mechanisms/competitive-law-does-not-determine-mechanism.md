# The competitive rate law does not determine the mechanism

Two different competitive mechanisms, one with a single dead-end complex $EI$ and one whose $EI$ isomerizes to a second dead-end form, give identical steady-state rate laws. Rate data of competitive form therefore cannot identify the mechanism, and the competitive constant need not be an elementary dissociation constant.

Let $k_1, k_2 > 0$, $k_{-1} \ge 0$, $K_M = (k_{-1} + k_2)/k_1$, $e_T > 0$, and fixed free
concentrations $s, i \ge 0$.

*Mechanism B* is the [competitive mechanism](competitive-inhibition-mechanism.md) with constants
$k_3, k_{-3} > 0$ extended by an isomerization of the inhibitor complex to a second dead-end form,
$EI \xrightarrow{k_5} EI^*$ and $EI^* \xrightarrow{k_{-5}} EI$ with $k_5, k_{-5} > 0$. Under the
steady-state premise (complex equations with $s, i$ frozen and $e + c + y + y^* = e_T$):

$$k_1 e s - (k_{-1} + k_2)c = 0, \quad k_3 e i - k_{-3} y - k_5 y + k_{-5} y^* = 0, \quad k_5 y - k_{-5} y^* = 0,$$

the solution is unique and the product rate is

$$v_B = \frac{k_2\, e_T\, s}{K_M\,(1 + i/K_B) + s}, \qquad K_B = \frac{k_{-3}/k_3}{1 + k_5/k_{-5}} .$$

*Mechanism A* is the competitive mechanism with the same $k_1, k_{-1}, k_2$ and any $k_3', k_{-3}' > 0$
with $k_{-3}'/k_3' = K_B$. By the
[competitive steady-state law](steady-state-rate-law-of-competitive-inhibition.md) its rate is
$v_A = k_2 e_T s/(K_M(1 + i/K_B) + s)$. Hence $v_A(s, i) = v_B(s, i)$ for all $s, i \ge 0$ and all
$e_T > 0$: both mechanisms are competitive as functions of the free inhibitor $i$, with the same $K_{ic} = K_B$. This classification does not assert linear competitive dependence on total inhibitor when depletion matters. In mechanism B the elementary
dissociation constant of $EI$ is $k_{-3}/k_3 > K_B$. For $i>0$, $K_{ic}=e\,i/(y+y^*)$ is the dissociation constant of all inhibitor-bound enzyme. At $i=0$ this ratio is undefined; $K_B$ remains defined by the positive rate constants.

## Depends on

- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)
- [Steady-state rate law of competitive inhibition](steady-state-rate-law-of-competitive-inhibition.md)

## Proof depends on

- [Competitive-inhibition mechanism](competitive-inhibition-mechanism.md)
- [Steady-state rate law of competitive inhibition](steady-state-rate-law-of-competitive-inhibition.md)

## Expansion

In mechanism B the third equation gives $y^* = (k_5/k_{-5})y$; substituted into the second it cancels
the isomerization terms, so $y = (i/K_I)e$ with $K_I = k_{-3}/k_3$, and $c = (s/K_M)e$. Conservation
gives $e(1 + s/K_M + (i/K_I)(1 + k_5/k_{-5})) = e_T$, and $v_B = k_2 c$ has the stated form. The $EI^*$ balance eliminates the net isomerization flux; the remaining $EI$ balance then fixes its binding ratio. Neither step requires a rapid-equilibrium approximation. Since the
two laws coincide as functions of $(s, i)$, no set of steady-state initial-rate measurements can tell
A from B; this is the general caution that kinetics can disprove a mechanism but never establish one,
and that inhibition constants are defined operationally, not as dissociation constants.

## Sources

- NC-IUB Panel on Enzyme Kinetics (A. Cornish-Bowden, H. B. F. Dixon, K. J. Laidler, I. H. Segel,
  J. Ricard, S. F. Velick and E. C. Webb), "Symbolism and terminology in enzyme kinetics,
  Recommendations 1981", *European Journal of Biochemistry* 128 (1982) 281–291; web version
  Section 4.2 ("An indefinitely large number of mechanisms generate Michaelis-Menten kinetics") and
  Section 6.4, last paragraph (whether an inhibition constant is a true dissociation constant "does not
  form part of the definitions"), <https://iubmb.qmul.ac.uk/kinetics/ek4t6.html>; Section 11 (a
  kinetic investigation "can never establish a mechanism beyond doubt"),
  <https://iubmb.qmul.ac.uk/kinetics/ek7.html>.
- A. Pesaresi, "Mixed and non-competitive enzyme inhibition: underlying mechanisms and mechanistic
  irrelevance of the formal two-site model", *Journal of Enzyme Inhibition and Medicinal Chemistry*
  38(1) (2023) 2245168, Introduction ("no bijective relation between the type of inhibition ... and
  the underlying molecular mechanisms"), <https://doi.org/10.1080/14756366.2023.2245168>.
