# Schnorr knowledge extractor

Let $q$ be a natural number. For
$r, s, r', s' \in \mathbb{Z}/q$ (the challenges and answers of two transcripts), the extracted
exponent is $(s - s')(r - r')^{-1} \in \mathbb{Z}/q$, where $u^{-1}$ is the inverse of $u$ in
$\mathbb{Z}/q$ when $u$ is a unit (and, otherwise, a conventional element of $\mathbb{Z}/q$
depending on $u$). For $q$ prime and $r \ne r'$ it is $(s - s')/(r - r')$.
