# Augmenting a catalog by the head of a list

Given a catalog $c$ and a list $L$ of
catalogs, the result is $c$ itself if $L$ is empty, and otherwise the sorted merge of $c$
with the sample (every other element, starting with the first) of the first catalog of $L$.
