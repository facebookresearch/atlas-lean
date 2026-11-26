# Consistent learners PAC-learn finite classes

Let $\alpha$ and $\beta$ be measurable spaces, $C$ a finite nonempty concept class of functions $\alpha \to \beta$ whose graphs $\{(x, y) : y = h(x)\}$ are measurable for every $h \in C$, and $A$ a learner from labeled samples of size $m$ that is consistent with $C$. Let $\varepsilon, \delta \in (0, 1)$ with

$$\frac{\log |C| + \log(1/\delta)}{\varepsilon} \le m .$$

Let $\mathcal{D}$ be any family of measures on $\alpha \times \beta$ each of which is realizable: of the form $D = P \circ (x \mapsto (x, c(x)))^{-1}$ for some probability measure $P$ on $\alpha$ and some measurable $c \in C$. Then $C$ is $(\varepsilon, \delta)$-PAC learnable with $m$ samples over $\mathcal{D}$: there is a learner (namely $A$) such that for every probability measure $D \in \mathcal{D}$,

$$D^{\otimes m}\big\{S : \mathrm{opt}_C(D) + \varepsilon < \mathrm{err}_D(A(S))\big\} \le \delta ,$$

where $\mathrm{opt}_C(D) = \inf_{h \in C} \mathrm{err}_D(h)$.
