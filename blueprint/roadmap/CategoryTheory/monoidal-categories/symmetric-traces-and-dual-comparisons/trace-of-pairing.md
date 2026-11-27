# Trace of a morphism along an exact pairing

Let $C$ be a symmetric monoidal category with symmetry $\beta$. Let $D$ be a right dual of $U$ through an exact pairing, with coevaluation $\eta_{U,D} : \mathbf{1} \to U \otimes D$ and evaluation $\varepsilon_{U,D} : D \otimes U \to \mathbf{1}$. For $f : X \otimes U \to Y \otimes U$, the trace $\operatorname{tr}_D(f) : X \to Y$ of $f$ along the pairing is the composite

$$X \cong X \otimes \mathbf{1} \xrightarrow{1_X \otimes \eta_{U,D}} X \otimes (U \otimes D) \cong (X \otimes U) \otimes D \xrightarrow{f \otimes 1_D} (Y \otimes U) \otimes D \cong Y \otimes (U \otimes D) \xrightarrow{1_Y \otimes \beta_{U,D}} Y \otimes (D \otimes U) \xrightarrow{1_Y \otimes \varepsilon_{U,D}} Y \otimes \mathbf{1} \cong Y,$$

where the unlabeled isomorphisms are unitors and associators. After $f$ the last two factors are $U \otimes D$; the symmetry $\beta_{U,D}$ puts them in the order $D \otimes U$ that the evaluation consumes.
