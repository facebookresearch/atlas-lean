# Laplace smoothing

Consider a multinomial naive Bayes model with a finite set of classes and a finite nonempty vocabulary $W$, and labelled documents given by word counts. For each class, Laplace (add-one) smoothing of its total word counts maximizes the unnormalized posterior of its word distribution under the Dirichlet prior with all concentrations $2$, over all probability vectors on $W$.
