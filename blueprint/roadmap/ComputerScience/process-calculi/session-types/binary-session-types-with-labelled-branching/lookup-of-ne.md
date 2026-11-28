# Context advancement preserves other channels up to permutation equivalence

If a typing context $\Delta$ results from [advancing](advances-2.md) channel $a$ of $\Gamma$ by an action, then for every channel $b \ne a$ the lookups of $b$ in $\Delta$ and $\Gamma$ are either both absent or both present with [permutation-equivalent](perm-equiv.md) types. The stored type at $b$ need not be identical: advancement is defined only up to [context permutation equivalence](perm-equiv-5.md), so it may reorder distinct branches at $b$.
