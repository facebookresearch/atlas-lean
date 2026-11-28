# Iris base logic

The *Iris base logic* is defined as a higher-order separation logic over a unital camera of resources: simply typed terms, the connectives of separation logic, ownership and validity, persistence, basic update and later modalities, and guarded recursion, interpreted in uniform predicates.

Fix $F$ and the solution $\mathit{iProp} \cong \mathrm{UPred}(\mathit{Res})$, $\mathit{Res} = F(\mathit{iProp})$ unital. Types and terms are

$$
\tau ::= M \mid \mathit{iProp} \mid 0 \mid 1 \mid \blacktriangleright \tau \mid \tau \times \tau \mid \tau + \tau \mid \tau \to \tau
$$

$$
t, P, Q ::= x \mid \mathrm{next}(t) \mid \lambda x{:}\tau.\, t \mid t(u) \mid a \mid |t| \mid t \cdot u \mid \mu x{:}\tau.\, t \mid \mathrm{False} \mid \mathrm{True} \mid t =_\tau u \mid P \Rightarrow Q \mid P \wedge Q \mid P \vee Q \mid P \ast Q \mid P \mathrel{-\!\!\ast} Q \mid \exists x{:}\tau.\, P \mid \forall x{:}\tau.\, P \mid \mathrm{Own}(t) \mid \mathcal{V}(t) \mid \square P \mid \triangleright P \mid \dot{|\!\Rrightarrow} P
$$

with pairs, sums and unit as usual, and simply typed, except that in $\mu x.\, t$ the variable $x$ may occur in $t$ only under $\triangleright$. Types are interpreted by $[\![\mathit{iProp}]\!] = \mathit{iProp}$, $[\![M]\!] = \mathit{Res}$, $[\![\blacktriangleright \tau]\!] = \blacktriangleright [\![\tau]\!]$ and $[\![\tau \to \sigma]\!] = [\![\tau]\!] \xrightarrow{ne} [\![\sigma]\!]$. Propositions in a variable assignment $\rho$ are interpreted by: $\mathrm{False} = \emptyset$, $\mathrm{True} = \mathbb{N}$ and $t = u$ as $\{ n \mid [\![t]\!] \overset{n}{=} [\![u]\!] \}$ at every resource; $\wedge, \vee, \forall, \exists$ pointwise by intersection and union;

- $(P \Rightarrow Q)(a) = \{ n \mid \forall m \le n,\ b.\ a \preccurlyeq b \land m \in \mathcal{V}(b) \land m \in P(b) \Rightarrow m \in Q(b) \}$;
- $(P \ast Q)(a) = \{ n \mid \exists b_1, b_2.\ a \overset{n}{=} b_1 \cdot b_2 \land n \in P(b_1) \land n \in Q(b_2) \}$;
- $(P \mathrel{-\!\!\ast} Q)(a) = \{ n \mid \forall m \le n,\ b.\ m \in \mathcal{V}(a \cdot b) \land m \in P(b) \Rightarrow m \in Q(a \cdot b) \}$;
- $\mathrm{Own}(t)(b) = \{ n \mid [\![t]\!] \overset{n}{\preccurlyeq} b \}$, $\mathcal{V}(t) = \mathcal{V}([\![t]\!])$ at every resource, and $(\square P)(a) = P(|a|)$;
- $\dot{|\!\Rrightarrow} P$ as on the basic-update page, $(\triangleright P)(a) = \{ n \mid n = 0 \lor n - 1 \in P(a) \}$, and $[\![\mu x.\, t]\!]_\rho = \mathrm{fix}(\lambda u.\, [\![t]\!]_{\rho[x \leftarrow u]})$. The *basic view shift* is the derived connective $P \mathrel{\dot{\Rrightarrow}} Q \triangleq \square(P \mathrel{-\!\!\ast} \dot{|\!\Rrightarrow} Q)$.

The judgment $\Gamma \mid P \vdash Q$ is derivable by the laws of intuitionistic higher-order logic with equality together with: EQ-REFL, EQ-LEIBNIZ and $\mathrm{next}(x) = \mathrm{next}(y) \dashv\vdash \triangleright(x = y)$; the affine bunched-implication laws for $\ast$ and $\mathrel{-\!\!\ast}$; $\mathrm{Own}(a) \ast \mathrm{Own}(b) \dashv\vdash \mathrm{Own}(a \cdot b)$, $\mathrm{True} \vdash \mathrm{Own}(\varepsilon)$, $\mathrm{Own}(a) \vdash \square \mathrm{Own}(|a|)$, $\mathrm{Own}(a) \vdash \mathcal{V}(a)$, $\mathcal{V}(a \cdot b) \vdash \mathcal{V}(a)$, $\mathcal{V}(a) \vdash \square \mathcal{V}(a)$; the basic-update laws UPD-MONO, UPD-INTRO, UPD-TRANS, UPD-FRAME, UPD-UPDATE; the persistence laws ($\square$-MONO, $\square P \vdash \square\square P$, $\square P \vdash P$, $\square P \wedge Q \vdash \square P \ast Q$, and commuting with $\forall, \exists$); the later laws ($\triangleright$-MONO, LÖB $(\triangleright P \Rightarrow P) \vdash P$, $\triangleright(P \ast Q) \dashv\vdash \triangleright P \ast \triangleright Q$, $\forall x.\, \triangleright P \vdash \triangleright \forall x.\, P$, $\triangleright \exists x.\, P \vdash \triangleright \mathrm{False} \vee \exists x.\, \triangleright P$, $\square \triangleright P \dashv\vdash \triangleright \square P$); and $\triangleright P \vdash \triangleright \mathrm{False} \vee (\triangleright \mathrm{False} \Rightarrow P)$, $\triangleright \mathrm{Own}(a) \vdash \exists b.\, \mathrm{Own}(b) \wedge \triangleright(a = b)$.

## Depends on

- [Solution of the Iris domain equation](solution-of-the-iris-domain-equation.md)
- [Uniform predicates](uniform-predicates.md)
- [Basic update modality](basic-update-modality.md)
- [Later OFE](../step-indexed-foundations/later-ofe.md)
- [Non-expansive and contractive maps](../step-indexed-foundations/non-expansive-and-contractive-maps.md)
- [Banach fixed-point theorem for complete OFEs](../step-indexed-foundations/banach-fixed-point-theorem-for-cofes.md)
- [Frame-preserving updates in cameras](../cameras/camera-frame-preserving-updates.md)

## Proof depends on

None.

## Expansion

Each connective's interpretation must satisfy the side conditions of uniform predicates, and the interpretation is non-expansive in the variable assignment; functions are interpreted as non-expansive functions, which is what justifies EQ-LEIBNIZ. The guardedness restriction makes the body of a recursive definition contractive, so the fixed point exists (the guarded fixed points page). The user may extend the logic with a signature of further types, terms and rules. The source's documentation lists the standard intuitionistic rules in full; the cited version of that documentation also has a plainness modality, with its laws and the rule UPD-PLAINLY, which the logic of the JFP article does not have and which is not part of the logic here.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 5 (grammar, typing and the guardedness restriction), Figure 10 (semantic interpretation), Figure 11 (proof rules) and Section 5.4 (the basic view shift), with footnote 13 on the full judgment.
- Iris Team, "The Iris 3.1 documentation", technical documentation (not peer reviewed) that the JFP article cites as its appendix (Iris Team, 2017), version of April 29, 2019, <https://plv.mpi-sws.org/iris/appendix-3.1.pdf>, Section 5.3 (the standard laws of intuitionistic higher-order logic with equality), supplementary.
