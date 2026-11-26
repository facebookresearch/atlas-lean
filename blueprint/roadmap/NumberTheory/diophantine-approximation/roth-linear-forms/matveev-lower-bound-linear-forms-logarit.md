# Matveev's lower bound for linear forms in logarithms (real case)

Let $L$ be a number
field of degree $D = [L : \mathbb{Q}]$ with a field embedding $f : L \to \mathbb{R}$, let $s \ge 1$
be a natural number, and let $\eta_1, \dots, \eta_s \in L$ satisfy $\eta_i \ne 1$ and
$f(\eta_i) > 0$ for every $i$. Let $d_1, \dots, d_s$ be nonzero integers and let $B$ be a real
number with $B \ge 1$ and $|d_i| \le B$ for every $i$. Let $A_1, \dots, A_s$ be real numbers with
$A_j \ge \max(D\,h(\eta_j), |\log f(\eta_j)|, 0.16)$ for every $j$, where $h$ is the absolute
logarithmic Weil height. Put $\Gamma = f(\eta_1)^{d_1} \cdots f(\eta_s)^{d_s} - 1$. If
$\Gamma \ne 0$, then

$$\log|\Gamma| > -1.4 \cdot 30^{s+3} \, s^{4.5} \, D^2 (1 + \log D)(1 + \log B) \, A_1 \cdots A_s.$$

No integrality is assumed on the $\eta_i$, so the statement also covers non-integral algebraic
numbers, such as the element in the source's application whose minimal polynomial has leading
coefficient $23$. The source states the bound with $B = \max_i |d_i|$; since the right-hand side
increases with $B$, any real $B \ge 1$ bounding every $|d_i|$ may be used.

## Sources

- Salah Eddine Rihane, Chèfiath Awero Adegbindin, and Alain Togbé, "Fermat Padovan And Perrin Numbers", Journal of Integer Sequences 23 (2020), Article 20.6.2, Section 2.1 and its Matveev theorem. Source URL <https://cs.uwaterloo.ca/journals/JIS/VOL23/Togbe/togbe16.tex>, definitions-and-theorem source lines 148–178, theorem lines 172–178. The source cites Bugeaud–Mignotte–Siksek, Theorem 9.4, as a modified consequence of E. M. Matveev, "An explicit lower bound for a homogeneous rational linear form in the logarithms of algebraic numbers, II", Izv. Math. 64 (2000), 1217–1269.
