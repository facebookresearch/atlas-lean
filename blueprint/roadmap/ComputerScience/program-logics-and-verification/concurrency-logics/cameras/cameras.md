# Cameras

A *camera* is defined as the step-indexed generalisation of a resource algebra: its carrier is an OFE, its operations are non-expansive, and validity becomes a step-indexed proposition. Cameras are the ghost-state structures over which Iris is parameterised.

A camera is a tuple $(M, \mathcal{V}, |\cdot|, \cdot)$ of an OFE $M$, a non-expansive validity $\mathcal{V} : M \xrightarrow{ne} \mathrm{SProp}$, a non-expansive partial core $|\cdot| : M \xrightarrow{ne} M^?$ and a non-expansive composition $\cdot : M \times M \xrightarrow{ne} M$, where $M^? = M \uplus \{\bot\}$ and composition is lifted by $a^? \cdot \bot = \bot \cdot a^? = a^?$, such that for all $n, a, b, c, b_1, b_2$:

- $(a \cdot b) \cdot c = a \cdot (b \cdot c)$ and $a \cdot b = b \cdot a$;
- if $|a| \in M$ then $|a| \cdot a = a$ and $||a|| = |a|$;
- if $|a| \in M$ and $a \preccurlyeq b$ then $|b| \in M$ and $|a| \preccurlyeq |b|$;
- $\mathcal{V}(a \cdot b) \subseteq \mathcal{V}(a)$;
- if $n \in \mathcal{V}(a)$ and $a \overset{n}{=} b_1 \cdot b_2$, then there are $c_1, c_2$ with $a = c_1 \cdot c_2$, $c_1 \overset{n}{=} b_1$ and $c_2 \overset{n}{=} b_2$;

where $a \preccurlyeq b \iff \exists c.\ b = a \cdot c$ and $a \overset{n}{\preccurlyeq} b \iff \exists c.\ b \overset{n}{=} a \cdot c$. A camera is *unital* if it has an element $\varepsilon$ that is valid at every index, satisfies $\varepsilon \cdot a = a$ for all $a$, and has $|\varepsilon| = \varepsilon$.

## Depends on

- [Resource algebras](../resource-algebras.md)
- [Ordered families of equivalences](../step-indexed-foundations/ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](../step-indexed-foundations/non-expansive-and-contractive-maps.md)
- [Step-indexed propositions](../step-indexed-foundations/step-indexed-propositions.md)

## Proof depends on

None.

## Expansion

The differences from resource algebras listed by the source: the carrier is an OFE, the core and composition are non-expansive, validity is a non-expansive step-indexed predicate, validity of a composition is contained in validity of a part at every index, and the extension axiom says decomposition commutes with step-indexed equality (it is needed for the rule $\triangleright(P \ast Q) \vdash \triangleright P \ast \triangleright Q$). In a unital camera the core is total, so both inclusions are reflexive, which is the case used for uniform predicates. The name began as a pronunciation of CMRA; the source no longer requires the carrier to be complete.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 4.4 and Figure 9 (camera axioms CAMERA-ASSOC, CAMERA-COMM, CAMERA-CORE-ID, CAMERA-CORE-IDEM, CAMERA-CORE-MONO, CAMERA-VALID-OP, CAMERA-EXTEND and the inclusions), Figure 3 (unital resource algebras) and footnotes 9-10.
