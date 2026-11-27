# Running a generic-group program with a fixed encoding

Let $q > 1$ and let $\mathrm{enc}$ be a permutation of $\mathbb{Z}/q$ encoding exponents as labels. For input labels $\mathit{inputs} : \{0, \dots, n-1\} \to \mathbb{Z}/q$ and a generic-group program $p$ over $n$ indices, the run [compiles](compile.md) $p$ in the environment $\mathit{inputs}$ and runs the resulting oracle computation against the [oracle of $\mathrm{enc}$](oracle-of.md).

The input labels are arbitrary. The program syntax cannot manufacture a literal label: every label it uses is an initial input or a previous oracle answer.
