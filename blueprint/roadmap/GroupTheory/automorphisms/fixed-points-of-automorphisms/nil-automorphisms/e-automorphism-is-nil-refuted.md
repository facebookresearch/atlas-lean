# An $e$-automorphism need not be a nil-automorphism

Vilyatser's assertion in Kourovka
Problem 11.23 is false: there are a group $G$ and an automorphism $\varphi$ of $G$ that is an
$e$-automorphism (for any subgroups $A$ and $B$ of $G$ with $\varphi(A) = A$, $\varphi(B) = B$ and
$A \not\subseteq B$, some $a \in A \setminus B$ has $a^{-1} \varphi(a) \in B$) but not a
nil-automorphism: writing $\delta(x) = x^{-1} \varphi(x)$, some $a \in G$ has $\delta^n(a) \ne 1$
for every $n \ge 0$.

Muliarchyk shows that the cyclic shift of order four on the fourth direct power of the first
Grigorchuk group is such an automorphism, using Bartholdi's characterization of the Engel elements
of the Grigorchuk group; the preprint states that the work was carried out with assistance from
ChatGPT. The Kourovka Notebook (21st issue) marks 11.23 solved, "No, not every".

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 11.23 (V. G. Vilyatser); resolution: K. Muliarchyk, An e-automorphism that is not a nil-automorphism, preprint (2026), main theorem: the cyclic shift `(g₀, g₁, g₂, g₃) ↦ (g₁, g₂, g₃, g₀)` on `Γ⁴`, `Γ` the first Grigorchuk group, is an `e`-automorphism of order four and not a nil-automorphism; the Kourovka Notebook (21st issue) marks 11.23 solved, https://kourovkanotebookorg.wordpress.com/wp-content/uploads/2026/09/kourovka_11_23_solution.pdf.
