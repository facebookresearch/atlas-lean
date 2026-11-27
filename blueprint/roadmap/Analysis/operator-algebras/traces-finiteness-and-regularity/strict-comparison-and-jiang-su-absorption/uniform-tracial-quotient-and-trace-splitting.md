# Uniform tracial quotient and all-order trace splitting

For a nonempty family $(\tau_i)$ of tracial states of a unital complex algebra $D$, use $\|x\|_{2,u}=\sup_i\sqrt{\mathrm{Re}\,\tau_i(x^*x)}$. The uniform tracial ultrapower at a free ultrafilter $\omega$ is the quotient of operator-norm-bounded sequences in $D$ by the ideal of sequences tending to zero in this uniform two-norm along $\omega$. For every sequence of indices $s=(s_j)$ the trace on the quotient is $\lambda_s([(x_j)])=\lim_\omega\tau_{s_j}(x_j)$. Write $\iota$ for constant images.

For each positive integer $m$, uniform trace splitting here asks for a family of $m$ self-adjoint projections $p_i$ in the quotient summing to its unit. They commute with all $\iota(a)$ for the specified input algebra, and for every $i,a,s$ satisfy $\lambda_s(\iota(a)p_i)=\lambda_s(\iota(a))/m$. For the unital result use $D=A$ and all tracial states. For the nonunital result let $D$ be the complex unitization of $A$ and use all norm-one positive linear traces on $A$ extended by $(z,a)\mapsto z+\tau(a)$. Test commutation and trace splitting on the image of $A$ in the unitization. Compactness of the normalized trace space, when required, is for the topology induced by the weak dual of $A$.

## Sources

- [Definitions in `Model.lean`, lines 2033–2042](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2033-L2042).
- [Definitions in `Model.lean`, lines 2074–2085](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2074-L2085).
- [Definitions in `Model.lean`, lines 2119–2122](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2119-L2122).
- [Definitions in `Model.lean`, lines 2176–2192](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2176-L2192).
- [Definitions in `Model.lean`, lines 2554–2579](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/JiangSu/Model.lean#L2554-L2579).
- [Definitions in `ChallengeDefinitions.lean`, lines 14–26](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/ChallengeDefinitions.lean#L14-L26).
- [Definitions in `Model.lean`, lines 34–36](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/Model.lean#L34-L36).
- [Definitions in `Model.lean`, lines 383–390](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/Model.lean#L383-L390).
- [Definitions in `Model.lean`, lines 469–470](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/Model.lean#L469-L470).
- [Definitions in `Model.lean`, lines 813–832](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/Model.lean#L813-L832).
- [Definitions in `Model.lean`, lines 956–967](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/TracialSplitting/Model.lean#L956-L967).
