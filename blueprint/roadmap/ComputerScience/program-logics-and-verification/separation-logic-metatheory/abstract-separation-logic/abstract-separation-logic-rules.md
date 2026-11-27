# Abstract separation logic

Over a [separation algebra](separation-algebras.md) $\Sigma$, commands are $C ::= c \mid \mathbf{skip} \mid C ; C \mid C + C \mid C^\ast$, with $c$ ranging over primitive commands, $+$ nondeterministic choice and $^\ast$ iterated sequential composition. A *valuation* $v$ maps each primitive command to a [local action](local-actions.md), and $[\![C]\!]v$ is the local action given by $[\![c]\!]v = v(c)$, $[\![\mathbf{skip}]\!]v\,\sigma = \{\sigma\}$, $[\![C_1 ; C_2]\!]v = [\![C_1]\!]v ; [\![C_2]\!]v$, $[\![C_1 + C_2]\!]v = [\![C_1]\!]v \sqcup [\![C_2]\!]v$ and $[\![C^\ast]\!]v = \bigsqcup_n [\![C^n]\!]v$, where $(f ; g)\sigma$ is $\top$ if $f\sigma = \top$ and $\bigsqcup\{g\sigma' : \sigma' \in f\sigma\}$ otherwise. A valuation *satisfies* a triple $\{p\}\, C\, \{q\}$ if $\langle\!\langle p \rangle\!\rangle\, [\![C]\!]v\, \langle\!\langle q \rangle\!\rangle$.

An *axiom set* $\mathit{Ax}$ is a set of triples $\{p\}\, c\, \{q\}$ for primitive commands with at least one for each primitive command. $\mathit{Ax} \vdash \{p\}\, C\, \{q\}$ means derivability from $\mathit{Ax}$ by the rules

- frame: from $\{p\}\, C\, \{q\}$ infer $\{p \ast r\}\, C\, \{q \ast r\}$;
- consequence: from $p' \subseteq p$, $\{p\}\, C\, \{q\}$ and $q \subseteq q'$ infer $\{p'\}\, C\, \{q'\}$;
- disjunction: from $\{p_i\}\, C\, \{q_i\}$ for all $i \in I$ infer $\{\bigcup_i p_i\}\, C\, \{\bigcup_i q_i\}$;
- conjunction: for $I \ne \emptyset$, from $\{p_i\}\, C\, \{q_i\}$ for all $i \in I$ infer $\{\bigcap_i p_i\}\, C\, \{\bigcap_i q_i\}$;
- $\{p\}\, \mathbf{skip}\, \{p\}$; from $\{p\}\, C_1\, \{q\}$ and $\{q\}\, C_2\, \{r\}$ infer $\{p\}\, C_1 ; C_2\, \{r\}$; from $\{p\}\, C_1\, \{q\}$ and $\{p\}\, C_2\, \{q\}$ infer $\{p\}\, C_1 + C_2\, \{q\}$; from $\{p\}\, C\, \{p\}$ infer $\{p\}\, C^\ast\, \{p\}$.

$\mathit{Ax} \models \{p\}\, C\, \{q\}$ means that every valuation satisfying all triples of $\mathit{Ax}$ satisfies $\{p\}\, C\, \{q\}$. Conditionals and loops are encoded with primitive $\mathrm{assume}$ commands, choice and iteration.

## Depends on

- [Local actions](local-actions.md)
- [Separation algebras](separation-algebras.md)

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007, pp. 366–378, <https://doi.org/10.1109/LICS.2007.30>, author copy <https://www.cs.ox.ac.uk/people/hongseok.yang/paper/asl-short.pdf>, Section 4 (Figure 1 and the encoding of conditionals and loops) and Section 5, Definitions 12–15 and Figure 2.
