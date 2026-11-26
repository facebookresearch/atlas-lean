# Ordered product of upper and lower block unipotents

Let R be any ring and α,β finite index types. For rectangular A:Matrix α β R and C:Matrix β α
R, put U(A)=[[I_α,A],[0,I_β]] and L(C)=[[I_α,0],[C,I_β]] in GL(α⊕β,R). For a list ℒ of either
α×β or β×α matrices, blockAltProd ℒ replaces a left-tagged A by U(A) and a right-tagged C by
L(C), then multiplies in list order. Thus blockAltProd []=I and
blockAltProd(a::ℒ)=E(a)*blockAltProd ℒ, where E selects U or L. Consecutive factors may have
the same tag.
