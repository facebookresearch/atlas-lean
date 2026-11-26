# Vardi-Wolper state bound for the LTL tableau

The formula size, the state count $2^{s}$ and the bound $2^{2s} = 4^{s}$ on the degeneralized state space are those of the [LTL model-checking construction](../model-checking-for-linear-temporal-logic/README.md): see its [formula size](../model-checking-for-linear-temporal-logic/size.md), [state count](../model-checking-for-linear-temporal-logic/nat-card-state.md) and [state bound](../model-checking-for-linear-temporal-logic/nat-card-buchi-state-le.md). The until-obligation bound is the [strict bound on fairness obligations](../model-checking-for-linear-temporal-logic/obligation-count-lt-size.md). The Vardi–Wolper automaton over the alphabet of sets of atoms is the [Vardi–Wolper translation with an exponential state bound](../model-checking-for-linear-temporal-logic/exists-buchi-card-le.md) at that alphabet, and the Büchi automaton for the general safety fragment is the [automaton for every LTL formula](../model-checking-for-linear-temporal-logic/exists-buchi.md) applied to the safety formula read in LTL.

## LTL

- [General safety fragment of LTL](safety-ext.md)

## Safety Ext

- [Safety formulas as LTL formulas](to-ltl.md)
