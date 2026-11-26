# Cokernel length is invariant under row and column reindexing

Let R be a commutative ring, n,n′ finite column types, m,m′ arbitrary row types, er:m≃m′,
ec:n≃n′ and A:Matrix m n R. Then length_R(R^m′/range((A.reindex er
ec).mulVecLin))=length_R(R^m/range(A.mulVecLin)).
