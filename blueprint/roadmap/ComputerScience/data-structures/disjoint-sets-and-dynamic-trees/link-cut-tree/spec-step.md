# Legal weighted link-cut operation

Legality and answers are determined by the represented
forest alone. A link requires a root and a vertex of a different tree; a cut requires a non-root.
Access preserves off-path preferences. Link makes the new edge solid after exposing both endpoints;
cut removes only the exposed incoming edge. Queries make the queried path solid, even when a
subsequent auxiliary splay brings the represented root to the top. The path answer multiplies
incoming edge weights in root-to-target order, excluding the root.
